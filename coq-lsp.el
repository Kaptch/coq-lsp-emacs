;;; coq-lsp.el --- Coq Client settings         -*- lexical-binding: t; -*-

;;; Commentary:

;; lsp-coq client

;;; Code:

(eval-when-compile
  (require 'rx)
  (require 'eglot)
  (require 'cl-lib)
  )
;; (require 'coq-mode)
(load-file "../coq-mode.el")
;; Mode description

(defgroup coq-lsp nil
  "Coq"
  :group 'elgot)

(defconst goals-buffer-name "*Goals*")
(defconst info-buffer-name "*Info*")

;; (defvar coq-mode-abbrev-table nil
;;   "Abbreviation table used in `coq-mode' buffers.")

;; (define-abbrev-table 'coq-mode-abbrev-table
;;   '())

;; (defvar coq-mode-map
;;   (let ((map (make-sparse-keymap)))
;;     (define-key map (kbd "C-c v") #'coq-lsp-refresh-window-layout)
;;     (define-key map (kbd "C-c C-k") #'eglot-shutdown)
;;     (define-key map (kbd "C-c c") #'coq-lsp-prove-till-cursor)
;;     (define-key map (kbd "C-c s") #'coq-lsp-get-doc)
;;     (define-key map (kbd "C-c d") #'coq-lsp-save-vo)
;;     map))

(defvar proof-mode-abbrev-table nil
  "Abbreviation table used in `proof-mode' buffers.")

(define-abbrev-table 'proof-mode-abbrev-table
  '())

(defvar proof-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c v") #'coq-lsp-refresh-window-layout)
    (define-key map (kbd "C-c C-k") #'eglot-shutdown)
    (define-key map (kbd "C-c c") #'coq-lsp-prove-till-cursor)
    (define-key map (kbd "C-c s") #'coq-lsp-get-doc)
    (define-key map (kbd "C-c d") #'coq-lsp-save-vo)
    map))

(add-hook 'eglot-managed-mode-hook
          (lambda ()
            ;; Show flymake diagnostics first.
            (setq eldoc-documentation-functions
                  (cons #'flymake-eldoc-function
                        (remove #'flymake-eldoc-function eldoc-documentation-functions)))
            ;; Show all eldoc feedback.
            (setq eldoc-documentation-strategy #'eldoc-documentation-compose)))

(define-derived-mode proof-mode prog-mode "Proof"
  "Major mode for coq files."
  :group 'coq-lsp
  (set 'compilation-mode-font-lock-keywords '())
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function)
  :abbrev-table coq-mode-abbrev-table)

;; (define-derived-mode coq-mode prog-mode "coq"
;;   "Major mode for coq files."
;;   :group 'coq-lsp
;;   (set 'compilation-mode-font-lock-keywords '())
;;   (set (make-local-variable 'lisp-indent-function)
;;        'common-lisp-indent-function)
;;   :abbrev-table coq-mode-abbrev-table)

(defvar proof-mode-status nil)
(defvar proof-mode-electric-terminator-mode nil)

;; Additional requests

(defun eglot--signal-proof/goals (position)
  "Send proof/goals to server, requesting the list of goals at POSITION."
  (let ((server (eglot-current-server))
        (params `(:textDocument ,(eglot--TextDocumentIdentifier)
                                :position ,position)))
    (if server
        (let ((response (jsonrpc-request server :proof/goals params)))
          (if response
              (let ((textDocumet (plist-get response :textDocument))
                    (position (plist-get response :position))
                    (goals (plist-get response :goals))
                    (messages (plist-get response :messages))
                    (err (plist-get response :error)))
                (coq-lsp--process-goal-info textDocumet position goals messages err)))))))

(defun eglot--signal-coq/document ()
  (let ((server (eglot-current-server))
        (params `(:textDocument ,(eglot--TextDocumentIdentifier))))
    (if server
        (let ((response (jsonrpc-request server :coq/getDocument params)))
          (if response
              (let ((spans (plist-get response :spans))
                    (completed (plist-get response :completed)))
                (coq-lsp--process-doc-info spans completed)))))))

(defun eglot--signal-coq/savevo ()
  (let ((server (eglot-current-server))
        (params `(:textDocument ,(eglot--TextDocumentIdentifier))))
    (if server
        (let ((response (jsonrpc-request server :coq/saveVo params)))
          (if response
              (progn ((coq-lsp--append-buffer-with-text info-buffer-name "Couldn't compile the file!\n\n"))))))))

;; Additional notifications
(cl-defmethod eglot-handle-notification
  (_server (_method (eql $/coq/fileProgress))
           &key textDocument processing)
  (let* ((uri (plist-get textDocument :uri))
         (lst (mapcar (lambda (elem) (list (plist-get elem :range) (plist-get elem :kind))) processing))q)
    (if-let ((buffer (find-buffer-visiting (eglot--uri-to-path uri))))
        (with-current-buffer buffer
          (dolist (elem lst)
            (let ((start (plist-get (plist-get (car elem) :start) :line))
                  (end (plist-get (plist-get (car elem) :end) :line))
                  (status (cdr elem)))
              (coq-lsp--process-notification start end status)))))))

;; Implementation

(defvar-local proof-line-position (list :pos 0 :buffer nil))

(defun coq-lsp--prove-till (pos)
  "Evaluate till POS and move the cursor to the end of evaluated region."
  (setq proof-line-position
        (list :pos pos :buffer (current-buffer)))
  (goto-char pos)
  (eglot--signal-proof/goals (eglot--pos-to-lsp-position)))

;; (defun coq-lsp--highlight-text (start end color)
;;   "Highlight text in COLOR from START to END in the current buffer."
;;   (let ((overlay (make-overlay start end)))
;;     (overlay-put overlay 'face '(:background color))))

;; ;; taken from lambdapi-proof.el
;; ;; taken from cus-edit.el
;; (defun coq-lsp--draw-horizontal-line ()
;;   "Draw a horizontal line at point.
;; This works for both graphical and text displays."
;;   (let ((p (point)))
;;     (insert "\n")
;;     (put-text-property p (1+ p) 'face '(:underline t))
;;     (overlay-put (make-overlay p (1+ p))
;;                  'before-string
;;                  (propertize "\n" 'face '(:underline t)
;;                              'display
;;                              (list 'space :align-to
;;                                    `(+ (0 . right)
;;                                        ,(min (window-hscroll)
;;                                              (- (line-end-position)
;;                                                 (line-beginning-position)))))))))

(defvar last-post-command-position 0
  "Holds the cursor position from the last run of post-command-hooks.")

(make-variable-buffer-local 'last-post-command-position)

(defun coq-lsp-prove-till-cursor-if-moved-post-command ()
  (unless (equal (point) last-post-command-position)
    (coq-lsp-prove-till-cursor))
  (setq last-post-command-position (point)))

(defun coq-lsp--pp-name-list (namelist)
  (substring (mapconcat (lambda (h) (format "%s, " h)) namelist "") 0 -2))

(defun coq-lsp--pp-hyp (hyp)
  (let ((hyp-names (plist-get hyp :names)))
    (let ((hyp-name (coq-lsp--pp-name-list hyp-names))
          (hyp-def (plist-get hyp :def))
          (hyp-ty (plist-get hyp :ty)))
      (cond (hyp-def (format "%s = %s : %s\n" hyp-name hyp-def hyp-ty))
            (t (format "%s : %s\n" hyp-name hyp-ty))
            ))))

(defun coq-lsp--pp-hyps (goals)
  (let ((goals (plist-get goals :goals)))
    (if (> (seq-length goals) 0)
        (let ((hyps (plist-get (seq-elt goals 0) :hyps)))
          (let ((hyps (seq-map 'coq-lsp--pp-hyp hyps)))
            (mapconcat (lambda (h) (format "%s" h)) hyps "")
            )))))

(defun coq-lsp--pp-goal (goals)
  (let ((goals (plist-get goals :goals)))
    (if (> (seq-length goals) 0)
        (plist-get (seq-elt goals 0) :ty))))

(defun coq-lsp--process-goal-info (textDocument position goals messages err)
  (coq-lsp--update-buffer-with-text goals-buffer-name (format "document:
  %s\nposition: %s\ngoals: %s\nmessages: %s\nerror: %s\n\n
State:\n
%s
===========================\n
%s\n" textDocument position goals messages err
  (coq-lsp--pp-hyps goals)
  (coq-lsp--pp-goal goals)
  )))

(defun coq-lsp--process-doc-info (spans completed)
  (coq-lsp--append-buffer-with-text info-buffer-name (format "spans: %s\ncompleted: %s\n\n" spans completed)))

(defun coq-lsp--process-notification (start end status)
  (coq-lsp--append-buffer-with-text info-buffer-name (format "start: %s\nend: %s\nstatus: %s\n\n" start end status)))

(defun coq-lsp--update-buffer-with-text (buffer-name text)
  "Create a new buffer or update an existing buffer named BUFFER-NAME with formatted TEXT."
  (with-current-buffer (get-buffer-create buffer-name)
    (read-only-mode -1)
    (erase-buffer)
    (insert text)
    (font-lock-fontify-buffer)
    (read-only-mode 1)
    (set-buffer-modified-p nil)))

(defun coq-lsp--append-buffer-with-text (buffer-name text)
  "Create a new buffer or append an existing buffer named BUFFER-NAME with formatted TEXT."
  (with-current-buffer (get-buffer-create buffer-name)
    (read-only-mode -1)
    (insert text)
    (font-lock-fontify-buffer)
    (read-only-mode 1)
    (set-buffer-modified-p nil)))

(defun get-current-window ()
  "Return the current window."
  (let ((all-windows (window-list)))
    (seq-find (lambda (w) (eq w (selected-window))) all-windows)))

;; Interface

(defun coq-lsp-prove-till-cursor ()
  "Proves till the command/tactic at cursor"
  (interactive)
  (coq-lsp--prove-till (point)))

(defun coq-lsp-get-doc ()
  "Return document"
  (interactive)
  (eglot--signal-coq/document))

(defun coq-lsp-save-vo ()
  "Save vo"
  (interactive)
  (eglot--signal-coq/savevo))

(defun coq-lsp--safe-split-window-vertically ()
  (if (<= (window-height) (* 2 window-min-height))
      (enlarge-window (+ 3 (* 2 window-min-height))))
  (split-window-vertically))

(defun coq-lsp--split-window-horizontally-1/3 ()
  "Split the current window horizontally, with the top part taking up 1/3 of the space."
  (let ((split-height-threshold nil))
    (split-window-below (/ (window-height) 3)))
  (other-window 1))

(defun coq-lsp--split-window-vertically-1/3 ()
  "Split the current window vertically, with the left part taking up 1/3 of the space."
  (interactive)
  (let ((split-width-threshold nil))
    (split-window-right (/ (window-width) 3)))
  (other-window 1))

(defun coq-lsp--split-window-vertically-2/3 ()
  "Split the current window vertically, with the left part taking up 2/3 of the space."
  (interactive)
  (let ((split-width-threshold nil))
    (split-window-right (* (/ (window-width) 3) 2)))
  (other-window 1))

(defun coq-lsp-refresh-window-layout ()
  "Create a 3-window layout with left window occupying half the screen, and two right windows stacked one on top of the other, with the two right windows read-only."
  (interactive)
  (let ((goals-buffer (get-buffer-create goals-buffer-name))
        (info-buffer (get-buffer-create info-buffer-name)))
    (with-current-buffer goals-buffer
      (read-only-mode 1))
    (with-current-buffer info-buffer
      (read-only-mode 1))
    (delete-other-windows)
    ;; (split-window-horizontally (round (* 0.5 (frame-width))))
    ;; (other-window 1)
    (coq-lsp--split-window-vertically-2/3)
    (set-window-buffer (get-current-window) goals-buffer)
    (with-selected-window (get-current-window)
      (set-window-dedicated-p (selected-window) t))
    ;; (split-window-vertically)
    (coq-lsp--safe-split-window-vertically)
    (other-window 1)
    (set-window-buffer (get-current-window) info-buffer)
    (with-selected-window (get-current-window)
      (set-window-dedicated-p (selected-window) t))
    (other-window 1)))

;; (add-hook 'post-command-hook #'coq-lsp-prove-till-cursor-if-moved-post-command)
;; (add-hook 'coq-mode-hook #'coq-lsp-prove-till-cursor-if-moved-post-command)

(add-to-list 'auto-mode-alist '("\\.v" . coq-mode))

(provide 'coq-lsp)
;;; coq-lsp.el ends here
