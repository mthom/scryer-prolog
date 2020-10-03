;;; showterm.el --- Show Prolog terms as trees in Emacs

;; Copyright (C) 2020 Markus Triska (triska@metalevel.at)

;; To try it, you need the following programs installed:
;;
;;     - Scryer Prolog
;;     - `dot' (from Graphviz)
;;     - `convert' (from ImageMagick)
;;
;; Copy showterm.el and showterm.pl to the same directory,
;; say ~/scryer-prolog/tools/, and add to your .emacs:
;;
;;     (load "~/scryer-prolog/tools/showterm.el")
;;
;; If necessary, set `scryer-prolog-path' to the Scryer Prolog
;; executable by adding to your .emacs (adapting as appropriate):
;;
;;     (setq scryer-prolog-path "/usr/local/bin/scryer-prolog")
;;
;; The function `showterm' draws the Prolog term in the region as a
;; tree. You can invoke it with M-x showterm RET, or for example by
;; binding it to a key in your .emacs, and then pressing that key:
;;
;;     (global-set-key [f12] 'showterm)
;;
;; Enjoy!

(defvar scryer-prolog-path
  (or (executable-find "scryer-prolog")
      "~/scryer-prolog/target/release/scryer-prolog")
  "Path of the Scryer Prolog executable.")

(defvar showterm-pl-file
  (format "%s%s"
          (if load-in-progress
              (file-name-directory load-file-name)
            default-directory)
          "showterm.pl")
  "Path to showterm.pl, used to produce a graph as input for `dot'.")

(defvar showterm-pixel-width 500
  "Width of the drawn term in pixels.")

(defun showterm (from to)
  (interactive "r")
  (unless (use-region-p)
    (error "No region"))
  (let ((str (buffer-substring-no-properties from to))
        op-declarations)
    (save-excursion
      ;; rudimentary support for op/3 directives.
      (goto-char (point-min))
      (while (re-search-forward "^:-[ \t]*\\(op(.*,.*,.*)[ \t]*\\.\\).*$" nil t)
        (push (match-string 1) op-declarations))
      (setq op-declarations (reverse op-declarations)))
    (with-temp-buffer
      (set-buffer-multibyte nil)
      (let ((proc (start-process "scryer-showterm" (current-buffer)
                                 scryer-prolog-path
                                 showterm-pl-file)))
        (showterm-wait-for-prompt)
        (while op-declarations
          (send-string proc (format "%s\n" (pop op-declarations)))
          (showterm-wait-for-prompt))
        (send-string proc (concat "dot, halt.\n" str " .\n"))
        (showterm-wait-for-process proc t)
        (setq str (buffer-string)))
      (erase-buffer)
      (let ((proc (start-process "dot" (current-buffer) "dot"
                                 "-Gdpi=300"
                                 "-T" "png")))
        (send-string proc str)
        (process-send-eof proc)
        (showterm-wait-for-process proc)
        (setq str (buffer-string))
        (erase-buffer))
      (let ((proc (let (process-connection-type)
                    (start-process "convert" (current-buffer)
                                   "convert"
                                   "png:-"
                                   "-gravity" "center"
                                   "-background" "white"
                                   "-scale" (format "%dx%d"
                                                    showterm-pixel-width
                                                    showterm-pixel-width)
                                   "-extent" (format "%dx" showterm-pixel-width)
                                   "png:-"))))
        (process-send-string proc str)
        (process-send-eof proc)
        (showterm-wait-for-process proc))
      (let ((img (create-image (buffer-string) 'png t))
            (fit-window-to-buffer-horizontally t)
            (buf (get-buffer-create "term-tree")))
        (with-current-buffer buf
          (erase-buffer)
          (setq mode-line-format ""
                cursor-in-non-selected-windows nil)
          (insert-image img)
          (insert "\n"))
        (fit-window-to-buffer (display-buffer-in-side-window buf '((side . right))))))))


(defun showterm-wait-for-prompt ()
  (let ((str (regexp-quote "?- "))
        seen)
    (while (not seen)
      (accept-process-output nil 0.01)
      (save-excursion
        (move-beginning-of-line nil)
        (setq seen (looking-at str))))
    (erase-buffer)))

(defun showterm-wait-for-process (proc &optional check-for-error)
  (set-process-sentinel proc (lambda (proc event)))
  (while (eq (process-status proc) 'run)
    (accept-process-output nil 0.1)
    (when check-for-error
      (goto-char (point-min))
      (when (looking-at "caught: error(syntax_error")
        (delete-process proc)
        (error "Syntax error, term cannot be displayed")))))
