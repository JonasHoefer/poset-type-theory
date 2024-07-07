;;; ctt.el --- Mode for the ctt programming language -*- lexical-binding: t -*-
;; Package-version: 1.0
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))
;; Keywords: languages

;;; Commentary:
;; This package provides a major mode for editing proofs or programs in poset type theroy.
;; It is based on cctt.el by Andras Kovacs (https://github.com/AndrasKovacs/cctt)

(require 'comint)
(require 'cl-lib)

;;;; Customization options

(defgroup ctt nil "Options for ctt-mode"
  :group 'languages
  :prefix 'ctt-
  :tag "ctt")

;;;; Syntax

(defvar ctt-keywords
  '("inductive" "higher" "import" "let" "in" "where" "module" "lock" "unlock")
  "Keywords.")

(defvar ctt-operations
  '("Ext" "Path" "PathP" "hComp" "coe" "refl" "U" "I" "ap" "split" ".1" ".2")
  "Operations.")

(defvar ctt-special
  '("undefined")
  "Special operators.")

(defvar ctt-keywords-regexp
  (regexp-opt ctt-keywords 'words)
  "Regexp that recognizes keywords.")

(defvar ctt-operations-regexp
  (regexp-opt ctt-operations 'words)
  "Regexp that recognizes operations.")

(defvar ctt-operators-regexp
  (regexp-opt '("," ":" "->" "→" "∙" "=" "|" "\\" "λ" "*" "×" "_" "@" "." "⁻¹" "[" "]" "/\\" "\\/") t)
  "Regexp that recognizes operators.")

(defvar ctt-special-regexp
  (regexp-opt ctt-special 'words)
  "Regexp that recognizes special operators.")

(defvar ctt-def-regexp "^[[:word:]'-/<>]+"
  "Regexp that recognizes the beginning of a definition.")

(defvar ctt-font-lock-keywords
  `((,ctt-keywords-regexp . font-lock-keyword-face)
    (,ctt-def-regexp . font-lock-function-name-face)
    (,ctt-operations-regexp . font-lock-builtin-face)
    (,ctt-operators-regexp . font-lock-variable-name-face)
    (,ctt-special-regexp . font-lock-warning-face))
  "Font-lock information, assigning each class of keyword a face.")

(defvar ctt-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  "_ 123" st)
    (modify-syntax-entry ?\n ">" st)
    (modify-syntax-entry ?\\ "." st)
    st)
  "Syntax table with Haskell-style comments.")

(defun ctt-indent-line ()
	"Indent current line."
	(insert-char ?\s 2))

;;;###autoload
(define-derived-mode ctt-mode prog-mode
  "ctt"
  "Major mode for editing ctt files."

  :syntax-table ctt-syntax-table

  ;; Make comment-dwim do the right thing for Cubical
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-end) "")

  ;; Code for syntax highlighting
  (setq font-lock-defaults '(ctt-font-lock-keywords))

	;; Indentation
	(setq indent-line-function 'ctt-indent-line)

  ;; Clear memory
  (setq ctt-keywords-regexp nil)
  (setq ctt-operators-regexp nil)
  (setq ctt-special-regexp nil))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ctt\\'" . ctt-mode))

(provide 'ctt-mode)
