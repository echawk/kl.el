;; shen.el --- Shen REPL for kl.el -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;; Author: Ethan Hawk
;; Maintainer: Ethan Hawk
;; URL: https://echawk.github.io
;; Version: 1.0.0
;; Package-Requires: ((emacs "30.2"))

;;; Commentary:

;; Interactive Shen support built on top of `kl.el'.

;;; Code:

(add-to-list 'load-path
             (file-name-directory (or load-file-name buffer-file-name)))

(require 'kl)
(require 'ring)
(require 'subr-x)

(defgroup shen nil
  "Shen support backed by the kl.el interpreter."
  :group 'languages)

(defcustom shen-repl-buffer-name "*Shen*"
  "Name of the Shen REPL buffer."
  :type 'string
  :group 'shen)

(defcustom shen-repl-input-ring-size 128
  "Maximum number of entries retained in Shen REPL input history."
  :type 'integer
  :group 'shen)

(defface shen-repl-prompt-face
  '((t :inherit font-lock-keyword-face :weight bold))
  "Face used for Shen prompts."
  :group 'shen)

(defvar shen--default-runtime nil)

(defvar-local shen--runtime nil)
(defvar-local shen--input-start nil)
(defvar-local shen--input-ring nil)
(defvar-local shen--history-index nil)
(defvar-local shen--saved-input "")

(defconst shen--completion-delimiters
  '(?\s ?\t ?\n ?\( ?\) ?\[ ?\] ?\{ ?\} ?\" ?\' ?\` ?, ?\;)
  "Characters that delimit Shen tokens in the REPL.")

(defun shen--make-runtime ()
  (let ((runtime (kl-runtime-reset)))
    (kl-load-kernel runtime)
    (kl-eval '(shen.initialise) runtime)
    runtime))

(defun shen--ensure-default-runtime ()
  (or shen--default-runtime
      (progn
        (message "Initializing Shen runtime...")
        (setq shen--default-runtime (shen--make-runtime))
        (message "Initializing Shen runtime...done")
        shen--default-runtime)))

(defun shen--ensure-buffer-runtime ()
  (or shen--runtime
      (progn
        (message "Initializing Shen REPL runtime...")
        (setq shen--runtime (shen--make-runtime))
        (message "Initializing Shen REPL runtime...done")
        shen--runtime)))

(defun shen--call-with-output (runtime form &optional input)
  (when input
    (kl-runtime-set-input-string runtime input))
  (kl-runtime-clear-output runtime)
  (kl-eval form runtime)
  (kl-runtime-drain-output runtime))

(defun shen--begin-turn (runtime)
  (kl-runtime-clear-output runtime)
  (kl-eval '(shen.initialise_environment) runtime))

(defun shen--prompt-string (runtime)
  (shen--begin-turn runtime)
  (shen--call-with-output runtime '(shen.prompt)))

(defun shen--normalize-input (string)
  (if (string-suffix-p "\n" string)
      string
    (concat string "\n")))

(defun shen/eval-string (string &optional runtime)
  "Evaluate STRING as one line of Shen REPL input.

Return the printed REPL output."
  (let ((runtime (or runtime
                     (if (derived-mode-p 'shen-repl-mode)
                         (shen--ensure-buffer-runtime)
                       (shen--ensure-default-runtime)))))
    (shen--begin-turn runtime)
    (shen--call-with-output
     runtime
     '(trap-error (shen.read-evaluate-print)
                  (lambda E (shen.toplevel-display-exception E)))
     (shen--normalize-input string))))

(defun shen--insert-read-only (string &optional face)
  (let ((inhibit-read-only t)
        (start (point-max)))
    (goto-char (point-max))
    (insert string)
    (add-text-properties
     start (point-max)
     `(read-only t
       rear-nonsticky (read-only)
       front-sticky (read-only)
       ,@(when face `(face ,face))))))

(defun shen--insert-prompt ()
  (let ((prompt (shen--prompt-string (shen--ensure-buffer-runtime))))
    (shen--insert-read-only prompt 'shen-repl-prompt-face)
    (set-marker shen--input-start (point-max))
    (goto-char (point-max))))

(defun shen--current-input ()
  (buffer-substring-no-properties (marker-position shen--input-start)
                                  (point-max)))

(defun shen--replace-current-input (string)
  (let ((inhibit-read-only t))
    (goto-char (marker-position shen--input-start))
    (delete-region (marker-position shen--input-start) (point-max))
    (insert string)))

(defun shen--seal-current-input ()
  (add-text-properties
   (marker-position shen--input-start) (point-max)
   '(read-only t rear-nonsticky (read-only) front-sticky (read-only))))

(defun shen--completion-runtime ()
  (or shen--runtime shen--default-runtime))

(defun shen--completion-token-char-p (char)
  (and char
       (not (memq char shen--completion-delimiters))))

(defun shen--bounds-of-token-at-point ()
  (when (and shen--input-start
             (>= (point) (marker-position shen--input-start)))
    (let ((origin (point))
          (limit (marker-position shen--input-start))
          start
          end)
      (save-excursion
        (while (and (> (point) limit)
                    (shen--completion-token-char-p (char-before)))
          (backward-char))
        (setq start (point))
        (goto-char origin)
        (while (shen--completion-token-char-p (char-after))
          (forward-char))
        (setq end (point)))
      (when (< start end)
        (cons start end)))))

(defun shen--completion-candidates (runtime)
  (let ((seen (make-hash-table :test 'equal))
        names)
    (dolist (symbol '(true false))
      (puthash (symbol-name symbol) t seen))
    (dolist (symbol kl-special-forms)
      (puthash (symbol-name symbol) t seen))
    (dolist (pair kl-primitive-arities)
      (puthash (symbol-name (car pair)) t seen))
    (maphash
     (lambda (symbol _value)
       (when (symbolp symbol)
         (puthash (symbol-name symbol) t seen)))
     (kl-runtime-functions runtime))
    (maphash
     (lambda (symbol _value)
       (when (symbolp symbol)
         (puthash (symbol-name symbol) t seen)))
     (kl-runtime-globals runtime))
    (maphash (lambda (name _present) (push name names)) seen)
    (sort names #'string<)))

(defun shen-repl-completion-at-point ()
  "Return completion data for the Shen REPL input at point."
  (let ((runtime (shen--completion-runtime))
        (bounds (shen--bounds-of-token-at-point)))
    (when (and runtime bounds)
      (list (car bounds)
            (cdr bounds)
            (completion-table-dynamic
             (lambda (_prefix)
               (shen--completion-candidates runtime)))
            :exclusive 'no))))

(defun shen--record-input (input)
  (unless (string-blank-p input)
    (ring-insert shen--input-ring input))
  (setq shen--history-index nil
        shen--saved-input ""))

(defun shen-repl-return ()
  "Evaluate the current Shen input."
  (interactive)
  (when (< (point) (marker-position shen--input-start))
    (goto-char (point-max)))
  (let* ((runtime (shen--ensure-buffer-runtime))
         (input (shen--current-input))
         (output (condition-case err
                     (shen/eval-string input runtime)
                   (error
                    (format "%s\n" (error-message-string err))))))
    (shen--record-input input)
    (shen--seal-current-input)
    (shen--insert-read-only "\n")
    (shen--insert-read-only output)
    (shen--insert-prompt)))

(defun shen-repl-previous-input ()
  "Replace current input with the previous REPL history entry."
  (interactive)
  (if (ring-empty-p shen--input-ring)
      (user-error "No Shen REPL history")
    (if shen--history-index
        (when (< (1+ shen--history-index) (ring-length shen--input-ring))
          (setq shen--history-index (1+ shen--history-index)))
      (setq shen--saved-input (shen--current-input)
            shen--history-index 0))
    (shen--replace-current-input (ring-ref shen--input-ring shen--history-index))
    (goto-char (point-max))))

(defun shen-repl-next-input ()
  "Replace current input with the next REPL history entry."
  (interactive)
  (unless shen--history-index
    (user-error "No newer Shen REPL history"))
  (if (zerop shen--history-index)
      (progn
        (setq shen--history-index nil)
        (shen--replace-current-input shen--saved-input))
    (setq shen--history-index (1- shen--history-index))
    (shen--replace-current-input (ring-ref shen--input-ring shen--history-index)))
  (goto-char (point-max)))

(defun shen-repl-beginning-of-line ()
  "Move to the start of the editable Shen input."
  (interactive)
  (if (>= (point) (marker-position shen--input-start))
      (goto-char (marker-position shen--input-start))
    (move-beginning-of-line 1)))

(defun shen-repl-clear-buffer ()
  "Clear the Shen REPL buffer, keeping the current runtime."
  (interactive)
  (let ((inhibit-read-only t))
    (erase-buffer)
    (when shen--runtime
      (shen--insert-prompt))))

(defun shen-repl-reset ()
  "Reset the Shen REPL runtime and buffer."
  (interactive)
  (let ((inhibit-read-only t))
    (erase-buffer))
  (setq shen--runtime nil
        shen--history-index nil
        shen--saved-input "")
  (setq shen--input-ring (make-ring shen-repl-input-ring-size))
  (shen--ensure-buffer-runtime)
  (shen--insert-read-only
   (shen--call-with-output shen--runtime '(shen.credits)))
  (shen--insert-prompt))

(defvar shen-repl-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map text-mode-map)
    (define-key map (kbd "RET") #'shen-repl-return)
    (define-key map (kbd "TAB") #'completion-at-point)
    (define-key map (kbd "<tab>") #'completion-at-point)
    (define-key map (kbd "M-p") #'shen-repl-previous-input)
    (define-key map (kbd "M-n") #'shen-repl-next-input)
    (define-key map (kbd "C-a") #'shen-repl-beginning-of-line)
    (define-key map (kbd "C-c C-r") #'shen-repl-reset)
    (define-key map (kbd "C-c M-o") #'shen-repl-clear-buffer)
    map))

(define-derived-mode shen-repl-mode text-mode "Shen-REPL"
  "Major mode for interacting with a Shen runtime."
  (setq-local indent-line-function #'ignore)
  (setq-local comment-start ";")
  (setq-local comment-end "")
  (setq-local shen--input-ring (make-ring shen-repl-input-ring-size))
  (setq-local shen--history-index nil)
  (setq-local shen--saved-input "")
  (setq-local complete-at-point-functions '(shen-repl-completion-at-point))
  (setq-local shen--input-start (copy-marker (point-max) nil)))

(defun shen/repl (&optional reset)
  "Open a Shen REPL buffer.

With prefix argument RESET, reinitialize the runtime."
  (interactive "P")
  (let ((buffer (get-buffer-create shen-repl-buffer-name)))
    (pop-to-buffer buffer)
    (with-current-buffer buffer
      (unless (derived-mode-p 'shen-repl-mode)
        (shen-repl-mode))
      (when (or reset (null shen--runtime))
        (shen-repl-reset))
      (goto-char (point-max)))))

(defvar shen-test--runtime nil)

(ert-deftest shen-eval-string ()
  (let ((runtime (or shen-test--runtime
                     (setq shen-test--runtime (shen--make-runtime)))))
    (should (equal "3\n" (shen/eval-string "(+ 1 2)" runtime)))))

(ert-deftest shen-repl-return-prints-result ()
  (let ((runtime (or shen-test--runtime
                     (setq shen-test--runtime (shen--make-runtime)))))
    (with-temp-buffer
      (shen-repl-mode)
      (setq shen--runtime runtime)
      (shen--insert-read-only
       (shen--call-with-output shen--runtime '(shen.credits)))
      (shen--insert-prompt)
      (goto-char (point-max))
      (insert "(+ 1 2)")
      (shen-repl-return)
      (should (string-match-p (regexp-quote "\n3\n")
                              (buffer-string))))))

(ert-deftest shen-repl-completion-at-point-offers-runtime-symbols ()
  (let ((runtime (or shen-test--runtime
                     (setq shen-test--runtime (shen--make-runtime)))))
    (with-temp-buffer
      (shen-repl-mode)
      (setq shen--runtime runtime)
      (insert "(shen.ini")
      (set-marker shen--input-start (point-min))
      (goto-char (point-max))
      (pcase-let ((`(,start ,end ,table . ,_) (shen-repl-completion-at-point)))
        (should (equal "shen.ini"
                       (buffer-substring-no-properties start end)))
        (should (member "shen.initialise"
                        (all-completions "shen.ini" table)))))))

(provide 'shen)

;;; shen.el ends here
