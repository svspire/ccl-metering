# CCL-METERING

Tools for metering lisp functions and methods in CCL.
Heavily cribbed from Mark Kantrowitz' metering.lisp. The user interface and reporting formats are almost identical to that code, but this is a rewrite and independent of it. The word "monitor" and its derivatives in the other code are "meter" etc. here.

Also heavily cribbed from encapsulations.lisp from Digitool.

This is CCL-specific, where the MK version is not.

This code also has the very useful feature that it enables one to meter individual methods of a generic function separately, where MK's does not. (Of course, metering regular functions is also still supported).

This operates by essentially wrapping some advice around each metered method or function.
The function #'meter accepts the same syntax as #'advise except it takes fewer args since it already knows precisely what extra work it needs to do before and after the nominal function.
The function #'meter* works just like #'meter except when you give it a symbol referring to a generic function it automatically calls #'meter on all its methods.
The main user interface is #'with-metering.

# EXAMPLE
    (in-package :ccl)
    (with-metering (directory %path-cat %path-std-quotes  %unix-file-kind  ftd-ff-call-expand-function
                           %ff-call  get-foreign-namestring  %read-dir  %new-directory-p  %open-dir
                           %file*= %split-dir  %add-directory-result  %all-directories %stat
                           %directory %files-in-directory %some-specific %one-wild %process-directory-result)
                          (:exclusive 0.0)
                          (length (directory "ccl:**;*" :files t :directories nil :follow-links nil :include-emacs-lockfiles t)))