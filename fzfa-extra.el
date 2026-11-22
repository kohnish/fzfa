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
(defvar fzfa-grep-wgrep-mode)
(defvar fzfa-grep-wgrep-mode-map)
(defvar vertico--input)
(defvar vertico--candidates)

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

;; Set unconditionally at load time: the transform is only a defvar
;; assignment, safe before fzfa itself loads (`defvar' in fzfa.el
;; does not clobber an already-bound value), and every producer spawn
;; goes through `fzfa--spawn' which consults it.
(fzfa-extra--tramp-setup)

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
          (fzfa-extra--paint-match-overlays buf query))))))

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
    (fzfa--location-preview cand nil)
    (fzfa-extra--update-highlights)))

(defun fzfa-extra-grep-preview (cand session)
  "Preview a grep candidate, then highlight query matches in the file."
  (if (null cand)
      (fzfa-extra--preview-teardown)
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

;;; Buffer annotations

(defface fzfa-extra-annotation-path
  '((t :inherit completions-annotations))
  "Face for the file-path part of `fzfa-extra-annotate-buffer'."
  :group 'fzfa)

(defface fzfa-extra-annotation-status
  '((t :inherit font-lock-type-face))
  "Face for status flags in `fzfa-extra-annotate-buffer'."
  :group 'fzfa)

(defvar agent-shell--state)

(defun fzfa-extra-annotate-buffer (cand)
  "Annotate buffer-name CAND for `fzfa-buffer'-style pickers.

Shows the buffer's full file path (TRAMP paths kept verbatim),
compilation status for compilation buffers, and agent-shell
busy/idle state for agent-shell buffers.  Status flags get
`fzfa-extra-annotation-status' so they stand out from the path."
  (when-let* ((buf (get-buffer cand)))
    (let ((path (when-let* ((file (buffer-file-name buf)))
                  ;; TRAMP names must stay verbatim; locally ~/ is
                  ;; enough.
                  (if (file-remote-p file)
                      file
                    (abbreviate-file-name file))))
          (status nil))
      (with-current-buffer buf
        (when (derived-mode-p 'compilation-mode)
          (push (if (get-buffer-process buf) "compiling" "compiled")
                status))
        (when (bound-and-true-p agent-shell--state)
          (let* ((state agent-shell--state)
                 (busy (or (map-elt state :active-requests)
                           (eq (map-elt (map-elt state :heartbeat) :status)
                               'busy))))
            (push (if busy "agent:busy" "agent:idle") status))))
      (let ((status-str (mapconcat #'identity (nreverse status) " ")))
        (cond
         ((and path (not (string-empty-p status-str)))
          (concat (propertize path 'face 'fzfa-extra-annotation-path)
                  "   "
                  (propertize status-str
                              'face 'fzfa-extra-annotation-status)))
         (path (propertize path 'face 'fzfa-extra-annotation-path))
         ((not (string-empty-p status-str))
          (propertize status-str 'face 'fzfa-extra-annotation-status))
         (t nil))))))

;;; Commands

;; Entry points combining fzfa sources with this package's tweaks.
;; They are plain defuns (not autoloaded); `(require 'fzfa-extra)' is
;; expected in the user config anyway.

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
  "Like `fzfa-swiper', with occur-style exact-first ordering."
  (interactive)
  (require 'vertico)
  (require 'fzfa-emacs)
  (let ((fzf-native-filter-only-min-pool 1)
        (fzfa-extra--exact-first-order t))
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
                              :annotate #'fzfa-extra-annotate-buffer)))
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
  "Grep with exact content-only matching and wgrep export.

Only the text after FILE:LINE: is matched (not filenames), exact
substring hits are ordered first, and C-x C-s / C-w export the
current candidates to a wgrep-capable buffer."
  (interactive)
  (require 'vertico)
  (require 'fzfa-grep)
  (with-no-warnings
    (vertico--advice
     (lambda ()
       (let ((fzfa-fuzzy nil)
             (fzfa-extra--grep-content-only t))
         (when-let* ((r (fzfa-completing-read
                         :command fzfa-grep-command
                         :category 'fzfa-grep
                         :group #'fzfa-extra-grep-group)))
           (fzfa-visit-grep r)))))))

(defun fzfa-extra--maybe-enable-vertico ()
  "Enable `vertico-mode' in minibuffers where `vertico--input' is active.

fzfa's display machinery keys off `vertico-mode'; enabling it only
inside fzfa sessions keeps global vertico state untouched."
  (when (bound-and-true-p vertico--input)
    (setq-local vertico-mode t)))

;;; Installation

(setq fzfa-preview-delay 0)

(add-hook 'minibuffer-setup-hook
          #'fzfa-extra--maybe-enable-vertico 90)
(add-hook 'minibuffer-setup-hook
          #'fzfa-extra--maybe-enable-grep-wgrep 90)

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
              #'fzfa-extra--grep-content-filter-advice))

(provide 'fzfa-extra)

;;; fzfa-extra.el ends here
