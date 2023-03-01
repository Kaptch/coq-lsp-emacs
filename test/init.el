(setq user-init-file (or load-file-name (buffer-file-name)))
(setq user-emacs-directory (file-name-directory user-init-file))
(setq package-user-dir "/home/kaptch/Projects/coq/test-lsp/emacs/.packages")
(setq inhibit-startup-screen t)

(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(setq package-enable-at-startup nil)
(package-initialize)
(when (not package-archive-contents)
  (package-refresh-contents))

(setq package-pinned-packages
      '((use-package . "melpa")))

(dolist (p (mapcar 'car package-pinned-packages))
  (unless (package-installed-p p)
    (package-install p)))

(use-package which-key
  :ensure t
  :config
  (add-hook 'after-init-hook 'which-key-mode))

(use-package swiper
  :ensure t
  :bind ("C-s" . swiper))

(use-package eglot
  :ensure t
  :commands eglot
  :config
  (add-to-list 'eglot-server-programs '(coq-mode . ("coq-lsp"))))

(add-hook 'coq-mode-hook 'eglot-ensure)

(load-file "../coq-lsp.el")
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(package-selected-packages '(coq use-package which-key swiper eglot)))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
