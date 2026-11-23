;;; fzfa-extra.el --- Optional enhancements for `fzfa' -*- lexical-binding: t; -*-

;; Copyright (C) 2026 James Nguyen

;; Author: James Nguyen <james@jojojames.com>
;; Version: 1.0
;; Package-Requires: ((emacs "29.1"))
;; Homepage: https://github.com/jojojames/fzfa
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:

;; A collection of fzfa enhancements, kept in one file so they can be
;; adopted or dropped independently of fzfa.el proper:
;;
;; - TRAMP support for `ssh' AND `sshx' methods: shell-command sources
;;   (`fzf-find', `fzf-grep', ...) are wrapped as
;;   `ssh HOST \='cd DIR && CMD\='' so fzf-native's local chdir never
;;   sees a /ssh: path.  Installed as
;;   `fzfa-source-spawn-transform-function', which `fzfa--spawn'
;;   already applies to every producer spawn.
;;
;; - Query-match highlighting in preview buffers: while an
;;   `fzfa-location' (occur/swiper) or `fzfa-grep' session previews a
;;   candidate, every literal occurrence of the minibuffer query in
;;   the previewed buffer gets an overlay — like swiper/occur.
;;   Overlays repaint on candidate AND query changes, are removed on
;;   session exit, and the origin window's point/scroll position is
;;   restored when the session is aborted (C-g).
;;
;; - Occur-style candidate ordering: a dynamic flag
;;   (`fzfa-extra--exact-first-order') that stable-partitions
;;   `fzfa-all-completions' results into literal query-substring
;;   matches first, then fuzzy-only matches, preserving fzfa's order
;;   within each group.  Combine with
;;   `fzf-native-filter-only-min-pool' for strict line order.
;;
;; - Grep content-only matching: a dynamic flag
;;   (`fzfa-extra--grep-content-only') that drops FILE:LINE:CONTENT
;;   candidates whose content portion doesn't contain the query, and
;;   strips fzf match-highlight faces from the FILE:LINE: prefix so
;;   the filename is never highlighted.  `fzfa-fuzzy' nil gives
;;   literal substring matching like helm-grep.
;;
;; - Grep result export: in fzfa grep minibuffers, C-x C-s writes the
;;   current candidates to a wgrep-capable grep-mode buffer (like
;;   `helm-grep-run-save-buffer'); C-w does the same and jumps
;;   straight into wgrep mode.
;;
;; - Preview toggle for buffer/grep pickers: `fzfa-buffer' and
;;   `fzfa-grep' sessions start with live preview OFF; C-c f toggles
;;   it helm-follow-style (off clears the preview, on previews the
;;   current candidate immediately).  Other categories keep fzfa's
;;   default preview behaviour.
;;
;; - Vertico prompt-selection retone: when the query matches nothing,
;;   vertico selects its "prompt" row and paints `vertico-current'
;;   (inheriting `highlight' — a loud background in many themes) over
;;   the whole typed input.  An advice swaps in the quieter
;;   `fzfa-extra-vertico-prompt-face' instead.
;;
;; Enable by requiring this file:
;;
;;   (require 'fzfa-extra)
;;
;; The dynamic flags are meant to be bound by wrapper commands, e.g.:
;;
;;   (defun my-fzf-occur ()
;;     (interactive)
;;     (let ((fzf-native-filter-only-min-pool 1)
;;           (fzfa-extra--exact-first-order t))
;;       (vertico--advice #'fzfa-swiper)))

;;; Code:

(require 'cl-lib)
(require 'map)

(defvar fzfa-preview-delay)
(defvar fzfa-fuzzy)
(defvar fzfa--active-sources)
(defvar fzfa--grep-line-regexp)
(defvar fzfa-source-spawn-transform-function)
(defvar fzfa-preview-functions)
(defvar fzfa-tramp-safe-local-dir)
(defvar completion-lazy-hilit-fn)
(defvar wgrep-line-file-regexp)
(defvar wgrep-header&footer-parser)
(defvar fzf-native-filter-only-min-pool)
(defvar fzfa-grep-command)
(defvar fzfa-rg-command)
(defvar fzfa-grep-wgrep-mode)
(defvar fzfa-grep-wgrep-mode-map)
(defvar compilation-in-progress)
(defvar vertico--input)
(defvar vertico--candidates)

(declare-function agent-shell-status "agent-shell")
(declare-function fzfa-preview-get "fzfa")
(declare-function fzfa-preview-show "fzfa")
(declare-function fzfa--location-preview "fzfa")
(declare-function fzfa--grep-preview "fzfa")
(declare-function fzfa-candidate-directory "fzfa")
(declare-function fzfa-completing-read "fzfa")
(declare-function fzfa-find "fzfa")
(declare-function fzfa-M-x "fzfa")
(declare-function fzfa-recent-file "fzfa")
(declare-function fzfa-swiper "fzfa")
(declare-function fzfa-visit-buffer "fzfa-emacs")
(declare-function fzfa-visit-grep "fzfa-grep")
(declare-function fzfa--max-columns-flag "fzfa")
(declare-function fzfa--preview-call "fzfa")
(declare-function fzfa--spawn "fzfa")
(declare-function fzfa-tramp--build-ssh-cmd "fzfa-tramp")
(declare-function tramp-dissect-file-name "tramp")
(declare-function tramp-file-name-method "tramp")
(declare-function wgrep-setup-internal "wgrep")
(declare-function wgrep-change-to-wgrep-mode "wgrep")

;;; Customization

(defcustom fzfa-extra-match-face 'isearch
  "Face used for query-match overlays in preview buffers."
  :type 'face
  :group 'fzfa)

(defcustom fzfa-extra-debug nil
  "When non-nil, log highlight repaint decisions to *fzfa-extra-log*."
  :type 'boolean
  :group 'fzfa)

;;; TRAMP

;;;###autoload
(defun fzfa-extra--ensure-tramp-transform (cmd dir)
  "Re-install `fzfa-extra--tramp-transform' if it was clobbered.

`fzfa--ensure-setup' calls `fzfa-tramp-setup' for the tramp
extension on the first fzfa command of a session, resetting
`fzfa-source-spawn-transform-function' to the ssh-only
`fzfa-tramp--transform'.  This :before advice on `fzfa--spawn'
restores ours — a superset that also handles sshx — whenever the
variable is nil or holds the built-in transform.  Custom transforms
installed by the user are left alone."
  (ignore cmd dir)
  (when (memq fzfa-source-spawn-transform-function
              '(nil fzfa-tramp--transform))
    (setq fzfa-source-spawn-transform-function
          #'fzfa-extra--tramp-transform)))

;;;###autoload
(defun fzfa-extra--tramp-transform (cmd dir)
  "Spawn transform for `fzfa-source-spawn-transform-function'.

For TRAMP `ssh' or `sshx'-method paths, wraps CMD as
`ssh HOST \\='cd LOCALNAME && CMD\\='' and returns
`fzfa-tramp-safe-local-dir' as the chdir target, so fzf-native's
local chdir never sees a remote path.  Other methods and local
paths pass through unchanged.  Unlike `fzfa-tramp--transform',
`sshx' is handled too — the wrapper invokes plain `ssh', which runs
the remote command through the remote shell either way."
  (if (not (file-remote-p dir))
      (cons cmd dir)
    (require 'tramp)
    (require 'fzfa-tramp)
    (let ((vec (tramp-dissect-file-name dir)))
      (if (member (tramp-file-name-method vec) '("ssh" "sshx"))
          (cons (fzfa-tramp--build-ssh-cmd vec cmd)
                fzfa-tramp-safe-local-dir)
        (cons cmd dir)))))

(defun fzfa-extra--tramp-setup ()
  "Install `fzfa-extra--tramp-transform' as the spawn transform."
  (setq fzfa-source-spawn-transform-function
        #'fzfa-extra--tramp-transform))

;; Install the transform eagerly via the autoloads file: the cookie
;; below makes `make autoloads' emit this form into
;; fzfa-autoloads.el, so package-activate sets the transform at
;; startup — before any picker runs and regardless of which fzfa
;; entry point is used.  `defvar' first so the setq binds the special
;; variable even when fzfa.el has not been loaded yet (its own defvar
;; will not clobber an already-bound value).
;;;###autoload
(progn
  (defvar fzfa-source-spawn-transform-function)
  (setq fzfa-source-spawn-transform-function
        #'fzfa-extra--tramp-transform)
  ;; `fzfa--ensure-setup' calls `fzfa-tramp-setup' on the first fzfa
  ;; command of a session, clobbering the transform with the ssh-only
  ;; built-in.  The :before advice on `fzfa--spawn' self-heals it at
  ;; spawn time; deferred so fzfa--spawn exists.
  (with-eval-after-load 'fzfa
    (advice-add 'fzfa--spawn :before
                #'fzfa-extra--ensure-tramp-transform)))

;;; Match highlighting in preview buffers

;; Session state lives in these globals, NOT in fzfa-preview-get/put:
;; `fzfa--preview-session' is dynamically bound to different cons cells
;; depending on the dispatch path (router plist vs per-source cell), so
;; state stored via fzfa-preview-put during a post-command-hook repaint
;; is invisible to the :preview/:exit handlers and vice versa — which is
;; how overlays could survive session teardown.
(defvar fzfa-extra--hl-overlays nil
  "Live match overlays painted by `fzfa-extra--update-highlights'.")
(defvar fzfa-extra--hl-sig nil
  "Last (BUFFER POINT QUERY) signature highlights were painted for.")
(defvar fzfa-extra--hl-disabled nil
  "Non-nil once the session began teardown; blocks further repaints.")
(defvar fzfa-extra--hl-orig-window nil
  "Origin window captured at :setup, for abort restore.")
(defvar fzfa-extra--hl-orig-point nil
  "Origin window point captured at :setup.")
(defvar fzfa-extra--hl-orig-start nil
  "Origin window start captured at :setup.")

(defun fzfa-extra--hl-log (fmt &rest args)
  (when fzfa-extra-debug
    (with-current-buffer (get-buffer-create "*fzfa-extra-log*")
      (goto-char (point-max))
      (insert (apply #'format (concat fmt "\n") args)))))

(defun fzfa-extra--clear-match-overlays ()
  (fzfa-extra--hl-log "clear: %d overlays" (length fzfa-extra--hl-overlays))
  (dolist (ov fzfa-extra--hl-overlays)
    (when (overlay-buffer ov) (delete-overlay ov)))
  (setq fzfa-extra--hl-overlays nil))

(defun fzfa-extra--paint-match-overlays (buf query)
  "Overlay every literal occurrence of QUERY in BUF."
  (with-current-buffer buf
    (save-excursion
      (save-restriction
        (widen)
        (let ((case-fold-search (not (string-match-p "[A-Z]" query)))
              (ovs nil))
          (goto-char (point-min))
          (while (re-search-forward (regexp-quote query) nil t)
            (let ((ov (make-overlay (match-beginning 0)
                                    (match-end 0) buf)))
              (overlay-put ov 'face fzfa-extra-match-face)
              (push ov ovs)))
          (setq fzfa-extra--hl-overlays (nreverse ovs))
          (fzfa-extra--hl-log "painted %d overlays in %S for %S"
                              (length ovs) buf query))))))

(defun fzfa-extra--update-highlights ()
  "Repaint query-match overlays if query/buffer/point changed.

Deduped on (BUFFER POINT QUERY) so post-command-hook ticks that
change nothing skip the buffer-wide search."
  (condition-case err
      (fzfa-extra--update-highlights-1)
    (error (fzfa-extra--hl-log "uh error: %S" err))))

(defun fzfa-extra--update-highlights-1 ()
  ;; Preview-suppressed sessions (C-c f off) must not paint overlays
  ;; either — this runs off the minibuffer's post-command-hook,
  ;; outside `fzfa--preview-call'.
  (if (fzfa-extra--preview-suppressed-p)
      (progn
        (setq fzfa-extra--hl-sig nil)
        (fzfa-extra--clear-match-overlays))
    (unless fzfa-extra--hl-disabled
    (let* ((win (fzfa-preview-get :origin-window))
           (buf (and (window-live-p win) (window-buffer win)))
           (mb (active-minibuffer-window))
           (query (and (window-live-p mb)
                       (with-current-buffer (window-buffer mb)
                         (minibuffer-contents-no-properties))))
           (sig (and buf (window-live-p win)
                     (list buf (window-point win) query))))
      (fzfa-extra--hl-log "uh: win=%S buf=%S pt=%S query=%S disabled=%S"
                          win buf (and (window-live-p win)
                                       (window-point win)) query
                          fzfa-extra--hl-disabled)
      (unless (equal sig fzfa-extra--hl-sig)
        (fzfa-extra--hl-log "uh: sig changed -> repaint")
        (setq fzfa-extra--hl-sig sig)
        (fzfa-extra--clear-match-overlays)
        (when (and buf (stringp query) (not (string-empty-p query)))
          (fzfa-extra--paint-match-overlays buf query)))))))

(defun fzfa-extra--preview-teardown ()
  "Clear match highlights and block further repaints."
  (setq fzfa-extra--hl-sig nil
        fzfa-extra--hl-disabled t)
  (fzfa-extra--clear-match-overlays))

(defun fzfa-extra-location-preview (cand _session)
  "Preview CAND's location, then highlight query matches in the buffer."
  (fzfa-extra--hl-log "preview: cand=%S" cand)
  (if (null cand)
      ;; Session teardown dispatches :preview with nil.
      (fzfa-extra--preview-teardown)
    ;; A live dispatch means preview is (back) on — clear the
    ;; teardown latch so match overlays repaint again.
    (setq fzfa-extra--hl-disabled nil)
    (fzfa--location-preview cand nil)
    (fzfa-extra--update-highlights)))

(defun fzfa-extra-grep-preview (cand session)
  "Preview a grep candidate, then highlight query matches in the file."
  (if (null cand)
      (fzfa-extra--preview-teardown)
    (setq fzfa-extra--hl-disabled nil)
    (when (fzfa--grep-preview cand session)
      (fzfa-extra--update-highlights))))

(defun fzfa-extra-location-preview-return (cand _session)
  "Restore the origin position when the session is aborted.

Runs after the minibuffer closes: CAND is nil on abort (C-g), the
selected candidate otherwise — in which case fzfa's own apply jumps
to the chosen location and there is nothing to restore."
  (when (null cand)
    (when-let* ((win fzfa-extra--hl-orig-window)
                ((window-live-p win))
                (buf (window-buffer win))
                ((buffer-live-p buf))
                (pt fzfa-extra--hl-orig-point)
                (st fzfa-extra--hl-orig-start))
      (with-selected-window win
        (when st (set-window-start win st))
        (goto-char pt)))))

(defun fzfa-extra-location-preview-setup ()
  "Repaint highlights on query changes that keep the same candidate.

fzfa only dispatches :preview when the highlighted candidate changes;
typing a query that leaves the top candidate unchanged would
otherwise never repaint the match overlays.  :setup runs in the
origin buffer's context, so the hook must be installed on the
minibuffer buffer explicitly."
  (setq fzfa-extra--hl-disabled nil
        fzfa-extra--hl-sig nil)
  (fzfa-extra--clear-match-overlays)
  (when-let* ((owin (fzfa-preview-get :origin-window))
              ((window-live-p owin)))
    (setq fzfa-extra--hl-orig-window owin
          fzfa-extra--hl-orig-point (window-point owin)
          fzfa-extra--hl-orig-start (window-start owin)))
  (when-let* ((mb (active-minibuffer-window))
              ((window-live-p mb))
              (mbuf (window-buffer mb)))
    (with-current-buffer mbuf
      (add-hook 'post-command-hook #'fzfa-extra--update-highlights nil t))))

;;; Candidate ordering and grep content filtering

(defvar fzfa-extra--occur-initial-input nil
  "When non-nil, injected as `:initial-input' into the
`fzfa-completing-read' call made by `fzfa-swiper'.  Bound by
`fzfa-extra-occur' so the picker opens pre-filled with the symbol
under point, like `helm-occur'.")

(defun fzfa-extra--inject-initial-input (orig &rest args)
  "Around-advice for `fzfa-completing-read'.

While `fzfa-extra--occur-initial-input' is bound, appends
`:initial-input' to ARGS unless the caller already supplied one.
Restricted to `fzfa-location' sessions so nested reads (e.g. an
interactive `:directory' prompt) inside the session are untouched."
  (if (and fzfa-extra--occur-initial-input
           (eq (plist-get args :category) 'fzfa-location)
           (not (plist-member args :initial-input)))
      (apply orig (append args
                          (list :initial-input
                                fzfa-extra--occur-initial-input)))
    (apply orig args)))

(defvar fzfa-extra--exact-first-order nil
  "When non-nil, exact query-substring matches sort ahead of
fuzzy-only matches in `fzfa-all-completions' (order preserved within
each group).  Bind around occur-style commands.")

(defvar fzfa-extra--grep-content-only nil
  "When non-nil, `fzfa-all-completions' keeps only grep candidates
whose CONTENT portion (after FILE:LINE:) contains the query —
fzf-native otherwise matches the whole FILE:LINE:CONTENT string,
including the filename.  Bind around grep commands.")

(defun fzfa-extra--exact-first-advice (orig &rest args)
  "Around-advice for `fzfa-all-completions'.

Stable-partitions CANDIDATES into exact substring matches of the
query first, then the rest — each group keeps the order fzfa/fzf
produced (line order under filter-only mode).  Only active for
`fzfa-location' candidates while `fzfa-extra--exact-first-order' is
bound."
  (let ((res (apply orig args)))
    (if (and fzfa-extra--exact-first-order
             (stringp (car args))
             (not (string-empty-p (car args)))
             (listp res)
             (> (length res) 1)
             (get-text-property 0 'fzfa-location (car res)))
        (let* ((re (regexp-quote (car args)))
               (case-fold-search
                (not (string-match-p "[A-Z]" (car args))))
               (exactp (lambda (c)
                         (and (stringp c) (string-match-p re c))))
               exact rest)
          (dolist (c res)
            (if (funcall exactp c)
                (push c exact)
              (push c rest)))
          (append (nreverse exact) (nreverse rest)))
      res)))

(defun fzfa-extra--grep-strip-prefix-faces (cand)
  "Return CAND with all text properties removed from its FILE:LINE:
prefix, so fzf match highlights never cover the filename."
  (if (and (stringp cand)
           (string-match fzfa--grep-line-regexp cand))
      (let ((end (match-end 0)))
        (concat (substring-no-properties cand 0 end)
                (substring cand end)))
    cand))

(defun fzfa-extra--grep-content-filter-advice (orig &rest args)
  "Around-advice for `fzfa-all-completions'.

Drops `FILE:LINE:CONTENT' candidates whose content does not contain
the query literally, so filename text can't produce matches, and
strips match-highlight faces from the FILE:LINE: prefix — fzf-native
marks positions over the whole candidate string, filename included.
Only active while `fzfa-extra--grep-content-only' is bound."
  (let ((res (apply orig args)))
    ;; Wrap vertico's display-time highlighter so it can't paint the
    ;; filename either (it re-highlights the whole candidate string).
    (when (and fzfa-extra--grep-content-only
               (bound-and-true-p completion-lazy-hilit-fn))
      (let ((orig-fn completion-lazy-hilit-fn))
        (setq completion-lazy-hilit-fn
              (lambda (cand)
                (fzfa-extra--grep-strip-prefix-faces
                 (funcall orig-fn cand))))))
    (if (and fzfa-extra--grep-content-only
             (stringp (car args))
             (not (string-empty-p (car args)))
             (listp res))
        (let* ((query (car args))
               (re (regexp-quote query))
               (case-fold-search
                (not (string-match-p "[A-Z]" query)))
               keep)
          (dolist (c res)
            (when (and (stringp c)
                       (string-match fzfa--grep-line-regexp c)
                       (string-match-p re
                                       (substring c (match-end 0))))
              (push (fzfa-extra--grep-strip-prefix-faces c) keep)))
          (nreverse keep))
      res)))

(defun fzfa-extra-grep-group (cand transform)
  "Group function for grep candidates.

Filename becomes the group header (vertico groups by it, preserving
grep's output order); TRANSFORM non-nil keeps the full
FILE:LINE:CONTENT string so the filename stays visible inline on
every candidate — unlike `fzfa--grep-group', which strips it."
  (if (string-match fzfa--grep-line-regexp cand)
      (if transform
          cand
        (match-string 1 cand))
    cand))

;;; Grep result export (wgrep)

(defvar fzfa-grep-wgrep-mode nil)
(make-variable-buffer-local 'fzfa-grep-wgrep-mode)

(defvar fzfa--preview-last)
(defvar fzfa--preview-run-fn)
(defvar fzfa--minibuffer-session)

(defvar fzfa-grep-wgrep-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-x C-s") #'fzfa-grep-save-results)
    (define-key map (kbd "C-w") #'fzfa-grep-wgrep)
    map)
  "Keymap for fzfa grep minibuffers; C-x C-s saves results for wgrep,
C-w saves and jumps straight into wgrep mode.")

(defun fzfa-extra--maybe-enable-grep-wgrep ()
  "In fzfa grep minibuffers, enable the wgrep export keymap."
  (when (and (bound-and-true-p vertico--input)
             (bound-and-true-p fzfa--active-sources)
             (vectorp fzfa--active-sources)
             (> (length fzfa--active-sources) 0)
             (seq-some (lambda (spec)
                         (eq (plist-get spec :category) 'fzfa-grep))
                       fzfa--active-sources))
    (setq-local fzfa-grep-wgrep-mode t)
    (setq-local minor-mode-map-alist
                (cons (cons 'fzfa-grep-wgrep-mode
                            fzfa-grep-wgrep-mode-map)
                      minor-mode-map-alist))))

(defun fzfa-grep--prepare-header&footer ()
  "wgrep header/footer parser for buffers from `fzfa-grep--write-results'.
Marks everything before the first FILE:LINE: result line read-only."
  (goto-char (point-min))
  (while (and (not (eobp))
              (not (looking-at wgrep-line-file-regexp)))
    (forward-line 1))
  (put-text-property (point-min) (point) 'read-only t)
  (put-text-property (point-min) (point) 'wgrep-header t))

(defun fzfa-grep--write-results ()
  "Write current fzfa grep candidates to a wgrep-capable buffer.
Returns the buffer.  The fzfa session is left running."
  (require 'wgrep)
  (require 'grep)
  (let* ((cands (or (bound-and-true-p vertico--candidates)
                    (and (boundp 'completion-all-sorted-completions)
                         completion-all-sorted-completions)))
         (lines nil)
         (dir (or (and (bound-and-true-p fzfa--active-sources)
                       (vectorp fzfa--active-sources)
                       (> (length fzfa--active-sources) 0)
                       (plist-get (aref fzfa--active-sources 0)
                                  :directory))
                  default-directory)))
    (dolist (c cands)
      (let ((s (if (consp c) (car c) c)))
        (when (stringp s)
          (push (substring-no-properties s) lines))))
    (setq lines (nreverse lines))
    (unless lines
      (user-error "No candidates to save"))
    (let* ((query (minibuffer-contents-no-properties))
           (i 1)
           name buf)
      (while (get-buffer (setq name
                               (format "*fzf-grep*%s"
                                       (if (= i 1) "" (format "<%d>" i)))))
        (setq i (1+ i)))
      (setq buf (get-buffer-create name))
      (with-current-buffer buf
        ;; Resolve relative FILE:LINE: paths the way grep produced them.
        (setq default-directory
              (cond ((file-directory-p dir)
                     (file-name-as-directory dir))
                    ((file-name-directory dir)
                     (file-name-as-directory (file-name-directory dir)))
                    (t default-directory)))
        (erase-buffer)
        (insert (format "fzf-grep results for `%s':\n\n" query))
        (dolist (l lines)
          (insert l "\n"))
        (setq buffer-read-only t)
        (grep-mode)
        (setq-local wgrep-header&footer-parser
                    #'fzfa-grep--prepare-header&footer)
        (unless (current-local-map)
          (use-local-map (make-sparse-keymap)))
        (wgrep-setup-internal))
      buf)))

(defun fzfa-grep-save-results ()
  "Save current fzfa grep candidates to a wgrep-capable buffer.
Writes all candidates matching the current query into a `grep-mode'
buffer (auto-named `*fzf-grep*', `*fzf-grep*<2>', ...) and keeps the
fzfa session open; exit it normally, then press C-c C-p
\\(wgrep-enable-key) in the results buffer to edit matches with wgrep."
  (interactive)
  (let ((buf (fzfa-grep--write-results)))
    (pop-to-buffer buf)
    (message "fzf-grep results saved in `%s'" (buffer-name buf))))

(defun fzfa-grep-wgrep ()
  "Save current fzfa grep candidates and jump straight into wgrep mode.
Like `fzfa-grep-save-results' but aborts the picker (restoring the
original position, like C-g) and opens the results buffer in
`wgrep-change-to-wgrep-mode' directly."
  (interactive)
  (let ((buf (fzfa-grep--write-results)))
    ;; Defer display + wgrep activation until after the minibuffer
    ;; unwind drains — fzfa documents this pattern for window changes.
    (add-hook 'minibuffer-exit-hook
              (lambda ()
                (run-at-time
                 0 nil
                 (lambda ()
                   (when (buffer-live-p buf)
                     (pop-to-buffer buf)
                     (wgrep-change-to-wgrep-mode)))))
              nil t)
    (abort-minibuffers)))

;;; Preview toggle (helm-follow-style)

(defvar fzfa--preview-last)
(defvar fzfa--preview-run-fn)
(defvar fzfa--minibuffer-session)

;; Buffer-local in the fzfa minibuffer: non-nil suppresses live
;; :preview dispatch.  Default ON for `fzfa-buffer' and `fzfa-grep'
;; pickers (see `fzfa-extra--maybe-enable-preview-toggle'); C-c f
;; flips it.  The gate lives in `fzfa-extra--preview-call-advice'
;; because fzfa fires previews from post-command-hook, idle timers,
;; and the frontend exhibit — all outside any dynamic binding the
;; command could let-bind.

(defvar-local fzfa-extra--preview-suppressed nil
  "Non-nil in an fzfa minibuffer where live preview is disabled.")

(defun fzfa-extra--preview-suppressed-p ()
  "Non-nil when the active fzfa minibuffer suppresses live preview.

Reads the flag from the minibuffer buffer (not the current one):
preview handlers run with the ORIGIN window/buffer selected, while
`fzfa-extra--update-highlights' runs from the minibuffer's
post-command-hook."
  (when-let* ((mb (active-minibuffer-window))
              ((window-live-p mb))
              (buf (window-buffer mb)))
    (buffer-local-value 'fzfa-extra--preview-suppressed buf)))

(defun fzfa-extra-toggle-preview ()
  "Toggle live preview in the current fzfa minibuffer.

Preview is off by default in `fzfa-buffer' and `fzfa-grep' pickers;
this switches it on — previewing the current candidate immediately —
or off, clearing the visible preview.  Bound to C-c f by
`fzfa-extra--maybe-enable-preview-toggle'."
  (interactive)
  (setq fzfa-extra--preview-suppressed
        (not fzfa-extra--preview-suppressed))
  (cond
   (fzfa-extra--preview-suppressed
    (message "fzfa preview: off")
    ;; Tear down whatever is currently previewed (nil cand dispatch).
    (when (and (boundp 'fzfa--minibuffer-session)
               fzfa--minibuffer-session)
      (fzfa--preview-call :preview fzfa--minibuffer-session nil)))
   (t
    (message "fzfa preview: on")
    ;; Force re-preview of the current candidate: `run' skips
    ;; candidates equal to `fzfa--preview-last', which was already
    ;; updated by the suppressed dispatches.
    (setq fzfa--preview-last 'unset)
    (when (functionp fzfa--preview-run-fn)
      (funcall fzfa--preview-run-fn)))))

(defun fzfa-extra--preview-call-advice (orig action session &rest args)
  "Around-advice for `fzfa--preview-call'.

Drops live :preview dispatches (non-nil CAND) while
`fzfa-extra--preview-suppressed' is set in the active minibuffer.
Teardown (:preview nil), :setup/:exit/:return, and explicit
`fzfa-preview-current' (C-c C-p) calls always pass through."
  (if (and (eq action :preview)
           (car args)
           (not (eq this-command 'fzfa-preview-current))
           (fzfa-extra--preview-suppressed-p))
      nil
    (apply orig action session args)))

(defvar fzfa-extra-preview-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c f") #'fzfa-extra-toggle-preview)
    map)
  "Keymap for fzfa-extra minibuffers; C-c f toggles live preview.")

(defvar fzfa-extra-preview-mode nil)
(make-variable-buffer-local 'fzfa-extra-preview-mode)

(defun fzfa-extra--maybe-enable-preview-toggle ()
  "In fzfa-buffer/fzfa-grep minibuffers, default preview off and
bind C-c f to `fzfa-extra-toggle-preview'."
  (when (and (bound-and-true-p fzfa--active-sources)
             (vectorp fzfa--active-sources)
             (> (length fzfa--active-sources) 0)
             (seq-some (lambda (spec)
                         (memq (plist-get spec :category)
                               '(fzfa-buffer fzfa-grep)))
                       fzfa--active-sources))
    (setq-local fzfa-extra--preview-suppressed t)
    (setq-local fzfa-extra-preview-mode t)
    (setq-local minor-mode-map-alist
                (cons (cons 'fzfa-extra-preview-mode
                            fzfa-extra-preview-mode-map)
                      minor-mode-map-alist))))

;;; Buffer annotations

(defface fzfa-extra-annotation-path
  '((t nil))
  "Face for the file-path part of `fzfa-extra-annotate-buffer'.
Deliberately empty: it only marks the text as propertized so vertico
does not paint it with the light-grey `completions-annotations'
face, while specifying no attributes lets the selection background
show through (inheriting `default' would pin the frame background
and hide it)."
  :group 'fzfa)

(defface fzfa-extra-annotation-status
  '((t :weight bold))
  "Face for idle status flags in `fzfa-extra-annotate-buffer'.
Bold default-face text stays readable on any theme, unlike the
light-grey `completions-annotations' face."
  :group 'fzfa)

(defface fzfa-extra-annotation-active
  '((t (:inherit font-lock-warning-face :weight bold)))
  "Face for active status flags (compiling, agent:busy, agent:waiting,
failed compilations)."
  :group 'fzfa)

(defvar agent-shell--state)

(defvar-local fzfa-extra--compile-exit nil
  "Exit status recorded for a finished compilation buffer.

Set by `fzfa-extra--record-compile-exit' on
`compilation-finish-functions': a number for normal exits, the
symbol `signal' when the process died by signal, nil when no status
was recorded (e.g. the buffer predates the hook).")

(defun fzfa-extra--record-compile-exit (buffer _msg)
  "Record BUFFER's compilation exit status in `fzfa-extra--compile-exit'.

Runs on `compilation-finish-functions', which fires while the
finished process is still on `compilation-in-progress' — stock
`compile' keeps no exit status, so this is the only place to grab
it.  Covers `ghostel-compile' too, which runs the same hook."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (when-let* ((proc (cl-find-if
                         (lambda (p) (eq (process-buffer p) buffer))
                         compilation-in-progress)))
        (setq fzfa-extra--compile-exit
              (or (process-exit-status proc) 'signal))))))

(defun fzfa-extra-annotate-buffer (cand)
  "Annotate buffer-name CAND for `fzfa-buffer'-style pickers.

Shows the buffer's full file path (TRAMP paths kept verbatim),
compilation status for compilation buffers (including the recorded
exit status once finished), and agent-shell busy/waiting/idle state
for agent-shell buffers.  The annotation is prefixed
with a \"│\" separator since single-source pickers append it right
after the candidate name; active states get
`fzfa-extra-annotation-active', idle ones
`fzfa-extra-annotation-status'."
  (when-let* ((buf (get-buffer cand)))
    (let ((path (when-let* ((file (buffer-file-name buf)))
                  ;; TRAMP names must stay verbatim; locally ~/ is
                  ;; enough.
                  (if (file-remote-p file)
                      file
                    (abbreviate-file-name file))))
          (status nil))
      (with-current-buffer buf
        (let ((proc (get-buffer-process buf)))
          ;; `compile' buffers report via `compilation-mode', but
          ;; `ghostel-compile' (behind `compile-with-buf-name') runs
          ;; in `ghostel-mode' instead.  Both push their process onto
          ;; `compilation-in-progress', which is the reliable
          ;; still-running signal across both.
          (when (or (derived-mode-p 'compilation-mode)
                    (and proc
                         (bound-and-true-p compilation-in-progress)
                         (memq proc compilation-in-progress)))
            (push (cond
                   (proc "compiling")
                   ((eq fzfa-extra--compile-exit 'signal)
                    "compiled:killed")
                   ((numberp fzfa-extra--compile-exit)
                    (if (zerop fzfa-extra--compile-exit)
                        "compiled:ok"
                      (format "compiled:exit %d" fzfa-extra--compile-exit)))
                   (t "compiled"))
                  status)))
        ;; A buffer-file-name that does not exist on disk means the
        ;; file was never saved (find-file on a new path still sets
        ;; buffer-file-name).  Skip the check for TRAMP paths —
        ;; file-exists-p there costs a remote round-trip per
        ;; candidate per redisplay.
        (when (and (buffer-file-name buf)
                   (not (file-remote-p (buffer-file-name buf)))
                   (not (file-exists-p (buffer-file-name buf))))
          (push "(unsaved)" status))
        ;; `agent-shell--state' is defvar-local WITH an init form, so
        ;; every buffer lazily gets a fresh non-nil state — the mode
        ;; check is what actually restricts this to agent-shell
        ;; buffers.  `agent-shell-status' distinguishes `blocked'
        ;; (waiting for a permission/elicitation answer) from plain
        ;; `busy'; fall back to the raw state flags on older versions.
        (when (and (derived-mode-p 'agent-shell-mode)
                   (bound-and-true-p agent-shell--state))
          (let* ((state agent-shell--state)
                 (status-sym
                  (or (and (fboundp 'agent-shell-status)
                           (ignore-errors
                             (agent-shell-status :shell-buffer buf)))
                      (if (or (map-elt state :active-requests)
                              (eq (map-elt (map-elt state :heartbeat)
                                           :status)
                                  'busy))
                          'busy
                        'ready))))
            (push (pcase status-sym
                    ('busy "agent:busy")
                    ('blocked "agent:waiting")
                    (_ "agent:idle"))
                  status))))
      (let* ((sep (propertize "    │ " 'face 'fzfa-extra-annotation-path))
             (path-str (and path
                            (propertize path
                                        'face 'fzfa-extra-annotation-path)))
             (status-str
              (mapconcat
               (lambda (s)
                 (propertize s 'face
                             (if (or (member s '("compiling" "agent:busy"
                                                  "agent:waiting"))
                                     (and (string-prefix-p "compiled:" s)
                                          (not (string= s "compiled:ok"))))
                                 'fzfa-extra-annotation-active
                               'fzfa-extra-annotation-status)))
               (nreverse status) " ")))
        (when (or path-str (not (string-empty-p status-str)))
          (concat sep
                  (cond
                   ((and path-str (not (string-empty-p status-str)))
                    (concat path-str "   " status-str))
                   (path-str path-str)
                   (t status-str))))))))

(defun fzfa-extra-buffer-affix (cands)
  "Affixation-function for `fzfa-extra-buffers'.

Annotates each candidate via `fzfa-extra-annotate-buffer' and pins
the annotation column just past the widest candidate name using a
`(space :align-to ...)' display spec — the same trick fzfa's
multi-source affix uses, since vertico concatenates suffixes
verbatim with no padding of its own."
  (let ((maxw (apply #'max 0 (mapcar #'string-width cands))))
    (cl-mapcar
     (lambda (cand)
       (let ((ann (fzfa-extra-annotate-buffer cand)))
         (list cand ""
               (if ann
                   (concat
                    (propertize " " 'display
                                `(space :align-to (+ left ,(+ maxw 2))))
                    ann)
                 ""))))
     cands)))

;;; Commands

;; Entry points combining fzfa sources with this package's tweaks.
;; All are ;;;###autoload-cookied so they work without an explicit
;; (require 'fzfa-extra); the first call loads the file, installing
;; hooks, advice, and the TRAMP transform.

;;;###autoload
(defun fzfa-extra-recentf ()
  "Like `fzfa-recent-file', but with previews disabled.

Previews open every recent file on each selection change, which is
too slow for large recentf lists."
  (interactive)
  (require 'vertico)
  (let ((fzfa-preview-delay nil))
    (with-no-warnings
      (vertico--advice #'fzfa-recent-file))))

;;;###autoload
(defun fzfa-extra-occur ()
  "Like `fzfa-swiper', with occur-style exact-first ordering.

Pre-fills the query with the symbol under point, like `helm-occur'."
  (interactive)
  (require 'vertico)
  (require 'fzfa-emacs)
  (let ((fzf-native-filter-only-min-pool 1)
        (fzfa-extra--exact-first-order t)
        (fzfa-extra--occur-initial-input (thing-at-point 'symbol)))
    (with-no-warnings
      (vertico--advice #'fzfa-swiper))))

;;;###autoload
(defun fzfa-extra-find ()
  "Like `fzfa-find'."
  (interactive)
  (require 'vertico)
  (with-no-warnings
    (vertico--advice #'fzfa-find)))

;;;###autoload
(defun fzfa-extra-buffers ()
  "Like `fzfa-buffer', annotated by `fzfa-extra-annotate-buffer'."
  (interactive)
  (require 'vertico)
  (require 'fzfa-emacs)
  (with-no-warnings
    (vertico--advice
     (lambda ()
       (let* ((names (cl-loop for b in (buffer-list)
                              unless (or (minibufferp b)
                                         (string-prefix-p " " (buffer-name b)))
                              collect (buffer-name b))))
         (when-let* ((result (fzfa-completing-read
                              :candidates names :prompt "buffer: "
                              :category 'fzfa-buffer
                              :annotate #'fzfa-extra-annotate-buffer
                              :affix #'fzfa-extra-buffer-affix)))
           (fzfa-visit-buffer result)))))))

;;;###autoload
(defun fzfa-extra-execute-command ()
  "Like `fzfa-M-x'."
  (interactive)
  (require 'vertico)
  (with-no-warnings
    (vertico--advice #'fzfa-M-x)))

;;;###autoload
(defun fzfa-extra-grep ()
  "Grep with rg (gitignore-aware) and wgrep export.

Uses `fzfa-rg-command' when rg is available — ripgrep respects
.gitignore/.ignore and skips hidden and binary files — falling back
to `fzfa-grep-command' otherwise.  Only the text after FILE:LINE: is
matched (not filenames), exact substring hits are ordered first,
and C-x C-s / C-w export the current candidates to a wgrep-capable
buffer."
  (interactive)
  (require 'vertico)
  (require 'fzfa-grep)
  (require 'fzfa-rg)
  (with-no-warnings
    (vertico--advice
     (lambda ()
       (let ((fzfa-fuzzy nil)
             (fzfa-extra--grep-content-only t)
             (cmd (if (executable-find "rg")
                      (format fzfa-rg-command
                              (fzfa--max-columns-flag 'rg))
                    fzfa-grep-command)))
         (when-let* ((r (fzfa-completing-read
                         :command cmd
                         :category 'fzfa-grep
                         :group #'fzfa-extra-grep-group)))
           (fzfa-visit-grep r)))))))

(defun fzfa-extra--maybe-enable-vertico ()
  "Enable `vertico-mode' in minibuffers where `vertico--input' is active.

fzfa's display machinery keys off `vertico-mode'; enabling it only
inside fzfa sessions keeps global vertico state untouched."
  (when (bound-and-true-p vertico--input)
    (setq-local vertico-mode t)))

;;; Vertico prompt-selection face

;; `vertico--prompt-selection' paints `vertico-current' over the whole
;; minibuffer input whenever the "prompt" pseudo-candidate is the
;; current selection — which is exactly what happens when the query
;; matches no candidates (`vertico--index' = -1).  `vertico-current'
;; inherits `highlight', a loud background colour in many themes
;; (k9's is blue), so a long specific query suddenly turns the typed
;; input blue.  The advice below swaps in a quieter face.

(defcustom fzfa-extra-vertico-prompt-face 'bold
  "Face for the minibuffer input while vertico's prompt row is current.

See `fzfa-extra--retone-vertico-prompt'.  Set to nil to keep
vertico's default `vertico-current' styling."
  :type '(choice (const :tag "Vertico default" nil) face)
  :group 'fzfa)

(defun fzfa-extra--retone-vertico-prompt ()
  "Swap `vertico-current' for `fzfa-extra-vertico-prompt-face' on input.

Runs right after `vertico--prompt-selection': replaces every
`vertico-current' mark between `minibuffer-prompt-end' and
`point-max' with `fzfa-extra-vertico-prompt-face', and removes the
latter again wherever `vertico-current' is absent, so the retone
tracks each exhibit instead of lingering between them."
  (when (and fzfa-extra-vertico-prompt-face (minibufferp))
    (let ((inhibit-modification-hooks t)
          (pos (minibuffer-prompt-end))
          (end (point-max)))
      (while (< pos end)
        (let* ((next (or (next-single-property-change pos 'face nil end)
                         end))
               (val  (get-text-property pos 'face)))
          (when (and val
                     (or (symbolp val)
                         (and (listp val)
                              (cl-every #'symbolp val))))
            (let* ((faces (if (listp val) val (list val)))
                   (new (cond
                         ((memq 'vertico-current faces)
                          (mapcar (lambda (f)
                                    (if (eq f 'vertico-current)
                                        fzfa-extra-vertico-prompt-face
                                      f))
                                  faces))
                         ((memq fzfa-extra-vertico-prompt-face faces)
                          (delq fzfa-extra-vertico-prompt-face faces)))))
              ;; A nil VALUE removes the `face' property.
              (put-text-property pos next 'face
                                 (cond ((null new) nil)
                                       ((and (null (cdr new))
                                             (symbolp val))
                                        (car new))
                                       (t new)))))
          (setq pos next))))))

(defun fzfa-extra--prompt-selection-advice (orig)
  "Around-advice for `vertico--prompt-selection'.
Retones the input face per `fzfa-extra-vertico-prompt-face'."
  (funcall orig)
  (fzfa-extra--retone-vertico-prompt))

;;; Installation

(setq fzfa-preview-delay 0)

(add-hook 'minibuffer-setup-hook
          #'fzfa-extra--maybe-enable-vertico 90)
(add-hook 'minibuffer-setup-hook
          #'fzfa-extra--maybe-enable-grep-wgrep 90)
(add-hook 'minibuffer-setup-hook
          #'fzfa-extra--maybe-enable-preview-toggle 90)

;; Record compilation exit statuses for `fzfa-extra-annotate-buffer'.
(with-eval-after-load 'compile
  (add-hook 'compilation-finish-functions
            #'fzfa-extra--record-compile-exit))

(with-eval-after-load 'fzfa
  ;; Shadow the default preview entries (alist-get takes the first
  ;; match): location previews additionally highlight query matches
  ;; and restore the origin position on abort; grep previews do the
  ;; same in the matched file (shown via display-buffer-same-window,
  ;; so the origin window's buffer IS the previewed file).
  (add-to-list 'fzfa-preview-functions
               '(fzfa-location
                 :setup   fzfa-extra-location-preview-setup
                 :preview fzfa-extra-location-preview
                 :exit    fzfa-extra--preview-teardown
                 :return  fzfa-extra-location-preview-return))
  (add-to-list 'fzfa-preview-functions
               '(fzfa-grep
                 :setup   fzfa-extra-location-preview-setup
                 :preview fzfa-extra-grep-preview
                 :exit    fzfa-extra--preview-teardown
                 :return  fzfa-extra-location-preview-return))
  ;; Occur-style exact-first ordering and grep content-only matching;
  ;; both are inert unless the corresponding dynamic flag is bound.
  (advice-add 'fzfa-all-completions :around
              #'fzfa-extra--exact-first-advice)
  (advice-add 'fzfa-all-completions :around
              #'fzfa-extra--grep-content-filter-advice)
  (advice-add 'fzfa--preview-call :around
              #'fzfa-extra--preview-call-advice)
  ;; `fzfa-extra-occur' pre-fill; inert unless the dynamic flag is bound.
  (advice-add 'fzfa-completing-read :around
              #'fzfa-extra--inject-initial-input))

;; Vertico is a separate package: fzfa loads it lazily, so the
;; prompt-selection advice waits for vertico itself.
(with-eval-after-load 'vertico
  (advice-add 'vertico--prompt-selection :around
              #'fzfa-extra--prompt-selection-advice))

(provide 'fzfa-extra)

;;; fzfa-extra.el ends here
