;;; CCL-metering.lisp
;;; Shannon Spires

;;; Tools for metering lisp functions and methods in CCL and MCL.
;;; Heavily cribbed from Mark Kantrowitz' metering.lisp. The user interface and
;;;   reporting formats are almost identical to that code, but this is a rewrite and independent of
;;;   it. The word "monitor" and its derivatives in the other code are "meter" etc. here.

;;; Also heavily cribbed from encapsulations.lisp from Digitool.

;;; This is MCL/CCL-specific, where the MK version is not. I'm of the opinion that it's
;;;   almost impossible to write truly portable, efficient metering code without it being
;;;   a rat's nest of compile-time feature switches, because metering is inherently
;;;   platform-specific. Thus this code is much simpler to read than MK's version.

;;; This code also has the very useful feature that it enables one to meter individual
;;;   methods of a generic function separately, where MK's does not. My code uses methods
;;;   heavily, and I often need to know which specific methods are taking the most time.
;;;   Thus this feature. (Of course, metering regular functions is also still supported).

;;; This operates by essentially wrapping some advice around each metered method or function.
;;; The function #'meter accepts the same syntax as #'advise except of course it takes fewer args
;;;   since it already knows precisely what extra work it needs to do before and after the nominal
;;;   function.
;;; The function #'meter* works just like #'meter except when you give it a symbol referring to a
;;;   generic function it automatically calls #'meter on all its methods.
;;; The main user interface is #'with-metering, which accepts the same args as #'with-monitoring
;;;   from the metering.lisp file.

;;; See examples at the end.

(in-package :ccl)

(export '(meter unmeter meter* with-metering with-metering* report-metering reset-all-metering
          metered-functions meter-all meter-form))

#+MCL
(set-dispatch-macro-character #\# #\> (lambda (stream char count) (declare (ignore stream char count)) (values)))

(defvar *meter-time-overhead* 0
  "The amount of time an empty metered function costs, in metering-time-units-per-second")
(defvar *meter-cons-overhead* 0
  "The amount of cons an empty metered function costs.")

(defvar *TOTAL-TIME* 0
  "Total amount of time metered so far.")
(defvar *TOTAL-CONS* 0
  "Total amount of consing metered so far.")
(defvar *TOTAL-CALLS* 0
  "Total number of calls metered so far.")
(defvar *TOTAL-OVERHEAD* 0
  "Total overhead so far.")
(defvar *no-calls* nil
  "A list of metered functions which weren't called.")
(defvar *estimated-total-overhead* 0)

(defparameter *metering-table*
  (make-hash-table :test #'equal))


;(defvar metering-time-units-per-second #+CCL-1.9 1000000000 #-CCL-1.9 1000000)
(defparameter metering-time-units-per-second 1000000)
(defparameter gc-time-conversion-factor (/ metering-time-units-per-second internal-time-units-per-second))

#+MCL
(defun microsecond-run-time ()
  (declare (special ccl::*cme-microseconds*))
  (rlet ((now :unsignedwide))
    (#_MicroSeconds now)
    (#_WideSubtract now ccl::*cme-microseconds*)
    (ccl::unsignedwide->integer now)))

; Can't use the one built in to CCL because its resolution is dependent on internal-time-units-per-second. This one is not.
#+OPENMCL
(defun %internal-microsecond-run-time ()
  ;; Returns user and system times in microseconds as multiple values.
  #-windows-target
  (rlet ((usage :rusage))
    (%%rusage usage)
    (let* ((user-seconds (pref usage :rusage.ru_utime.tv_sec))
           (system-seconds (pref usage :rusage.ru_stime.tv_sec))
           (user-micros (pref usage :rusage.ru_utime.tv_usec))
           (system-micros (pref usage :rusage.ru_stime.tv_usec)))
      (values (+ (* user-seconds 1000000)
                 (round user-micros 1))
              (+ (* system-seconds 1000000)
                 (round system-micros 1)))))
  #+windows-target
  (rlet ((start #>FILETIME)
         (end #>FILETIME)
         (kernel #>FILETIME)
         (user #>FILETIME))
    (#_GetProcessTimes (#_GetCurrentProcess) start end kernel user)
    (let* ((user-100ns (dpb (pref user #>FILETIME.dwHighDateTime)
                            (byte 32 32)
                            (pref user #>FILETIME.dwLowDateTime)))
           (kernel-100ns (dpb (pref kernel #>FILETIME.dwHighDateTime)
                            (byte 32 32)
                            (pref kernel #>FILETIME.dwLowDateTime)))
           (convert 1))
      (values (floor user-100ns convert) (floor kernel-100ns convert)))))

#+OPENMCL
(defun microsecond-run-time ()
  "Return the run time in the internal time format. (See
  INTERNAL-TIME-UNITS-PER-SECOND.) This is useful for finding CPU usage."
  (multiple-value-bind (user sys) (%internal-microsecond-run-time)
    (+ user sys)))

(defstruct (metering)
  (inclusive-time 0) ; time in metering-time-units-per-second
  (inclusive-cons 0)
  (exclusive-time 0) ; time in metering-time-units-per-second
  (exclusive-cons 0)
  (calls 0)
  (nested-calls 0)
)

(defstruct (metering-info 
           (:conc-name m-info-)
           (:constructor make-metering-info
                         (name calls time cons
                               percent-time percent-cons
                               time-per-call cons-per-call)))
  name
  calls
  time
  cons
  percent-time
  percent-cons
  time-per-call
  cons-per-call)

(defstruct (metering-column
            (:conc-name m-column-)
            (:constructor make-metering-column (header value-getter formatter justify totalize)))
  header ; string or list of strings. If the latter, each will be on a different line.
  value-getter
  formatter ; for values
  justify ; :left, :center, or :right
  totalize ; T to totalize column, nil to not, string to show string in lieu of total
  )

; Column instances for a particular printout
(defstruct column-instance
  column
  tabstop ; tab position of right-hand edge of this column
  total)

(defparameter *metering-columns*
  (list
   (make-metering-column "Function or Method" 'm-info-name "~A" :left "Total:")
   (make-metering-column '("%" "Time") 'm-info-percent-time "~,2F" :right t)
   (make-metering-column '("%" "Cons") 'm-info-percent-cons "~,2F" :right t)
   (make-metering-column "Calls" 'm-info-calls "~D" :right t)
   (make-metering-column "Sec/Call" 'm-info-time-per-call "~,6F" :right nil)
   (make-metering-column '("Cons" "Per" "Call") 'm-info-cons-per-call "~D" :right nil)
   (make-metering-column '("Total" "Time") 'm-info-time "~,6F" :right t)
   (make-metering-column '("Total" "Cons") 'm-info-cons "~D" :right t))
  "Descriptors of columns in metering results table"
  )
       
(defparameter *spaces-between-columns* 2 "Minimum number of spaces that should appear between columns")

(defun get-max-width-of-header (column)
  (let ((header (m-column-header column)))
    (if (listp header)
      (reduce 'max header :key 'length)
      (length header))))

(defun get-max-width (results filter column)
  "Returns the maximum width of all the values in this column, including the column header and final total, if any.
   Filter is a single-arg predicate which returns true if a particular result should be included in calculating
   total width."
  (let ((max-width (get-max-width-of-header column))
        (total 0)
        (totalize (m-column-totalize column)))
    ; Note: Don't get cute and assume total will always be widest thing in column. You might have a mix
    ;   of positive and negative numbers.
    (dolist (result results)
      (when (funcall filter result)
        (let ((value (funcall (m-column-value-getter column) result)))
          (when (eq t totalize) ; assume if totalize is t, everything in column is a number except for error cases
            (incf total (if (numberp value) value 0)))
          (setf max-width
                (max max-width
                     (length (format nil (m-column-formatter column) value)))))))
    (when totalize
      (setf max-width (max max-width (length (if (stringp totalize)
                                               totalize
                                               (format nil (m-column-formatter column) total)
                                               )))))
    max-width))
     
(defun init-tabstops (results filter column-instances)
  "Find tabstop of right-hand edge of each column."
  (let ((running-total (- *spaces-between-columns*))) ; so leftmost column's right-hand edge won't be affected by *spaces-between-columns*
    (loop for ci in column-instances do
      (let ((column (column-instance-column ci)))
        (setf (column-instance-tabstop ci)
              (incf running-total (+ *spaces-between-columns* (get-max-width results filter column))))))))

(defun lines-in-header (column)
  "How many lines will the header of this column require?"
  (let ((header (m-column-header column)))
    (if (listp header)
      (length header)
      1)))

(defun header-line (n column)
  "Get header-line n for column. Line 0 is bottommost, Line 1 is above that, etc."
  (let ((header (m-column-header column)))
    (if (listp header)
      (nth (- (1- (length header)) n) header)
      header)))

(defun print-cell (stream outstring justify beginning-of-column end-of-column)
  (let ((tabstop (case justify
                   (:right (- end-of-column (length outstring)))
                   (:left  beginning-of-column)
                   (:center (- (round (+ beginning-of-column end-of-column) 2)
                               (round (length outstring) 2))))))
    (format stream "~V,0T~A" tabstop outstring)))

(defun print-column-headers (stream results filter column-instances)
  "Print headers at beginning of table."
  (init-tabstops results filter column-instances)
  (let ((total-lines-in-header (reduce 'max column-instances
                                       :key (lambda (ci) (lines-in-header (column-instance-column ci))))))
    (loop for i from total-lines-in-header downto 1 do
      (format stream "~%")
      (let ((beginning-of-column 0))
        (loop for ci in column-instances do
          (let ((column (column-instance-column ci))
                (end-of-column (column-instance-tabstop ci)))
            (when (>= (lines-in-header column) i)
              (print-cell stream
                          (header-line (1- i) column)
                          (m-column-justify column)
                          beginning-of-column
                          end-of-column))
            (setf beginning-of-column end-of-column)))))
    (format stream "~%~V,,,'-A" (column-instance-tabstop (car (last column-instances))) "-")
    ))

(defun print-result (stream result column-instances)
  (let ((beginning-of-column 0))
    (loop for ci in column-instances do
      (let ((column (column-instance-column ci))
            (end-of-column (column-instance-tabstop ci)))
        (print-cell stream 
                    (format nil (m-column-formatter column) (funcall (m-column-value-getter column) result))
                    (m-column-justify column)
                    beginning-of-column
                    end-of-column)
        (setf beginning-of-column end-of-column)))))

(defun print-column-trailers (stream column-instances)
  (format stream "~V,,,'-A~%" (column-instance-tabstop (car (last column-instances))) "-")
  (let ((beginning-of-column 0))
    (loop for ci in column-instances do
      (let ((column (column-instance-column ci))
            (end-of-column (column-instance-tabstop ci))
            (total (column-instance-total ci)))
        (print-cell stream
                    (format nil (m-column-formatter column) (or total ""))
                    (m-column-justify column)
                    beginning-of-column
                    end-of-column)
        (setf beginning-of-column end-of-column)))))

;(defmacro get-time ()
;    `(the unsigned-byte (get-internal-run-time)))

; Note the bogosity here: Pre-CCL-1.9, we're measuring runtime. Post-CCL-1.9, we're measuring wall clock time.
; FIXED.
#+IGNORE ;#+(and openmcl ccl-1.9)
(defmacro get-time ()
  `(ccl:current-time-in-nanoseconds))

;#-(and openmcl ccl-1.9)
(defmacro get-time ()
  `(microsecond-run-time))

(defmacro get-gctime ()
  (* gc-time-conversion-factor (gctime)))

(defmacro get-cons () `(the unsigned-byte (ccl::total-bytes-allocated)))

(defun get-metering-stats (spec)
  (gethash spec *metering-table*))

(defun (setf get-metering-stats) (value spec)
  (setf (gethash spec *metering-table*) value))


#-MCL
(defun %unmeter-all ()
  (unadvise t :when :meter :name :meter)
  (clrhash *metering-table*))

#+MCL
(defun %unmeter-all ()
  (let (val)
    (dolist (capsule *advise-alist*)
      (when (eq :METER (encapsulation-advice-when capsule))
        (push (list (encapsulation-spec capsule)
                    (encapsulation-advice-when capsule)
                    (encapsulation-advice-name capsule))
              val)
        (remove-encapsulation capsule)))
     (clrhash *metering-table*) ; just a little extra insurance
      val))

; (unmeter t) will remove all metering advice
; (un t) will also remove all metering, as well as all other advice

(defun unmeter (function)
  (cond ((neq function t)
         #+MCL
         (unadvise-1 function :METER :METER)
         #-MCL
         (%unadvise-1 function :METER :METER)
         )
        (t (%unmeter-all))))


#+MCL
(let ((*warn-if-redefine-kernel* nil))
(defun remove-encapsulation (capsule &optional dont-replace)
  ; optional don't replace is for unadvising, tracing all on a method
  (let (spec nextsym newdef def)
    (setf spec (encapsulation-owner capsule))
    (setf def (typecase spec
                (symbol (fboundp spec))
                (method spec)))
    (setf nextsym (encapsulation-symbol capsule))
    (setf newdef (fboundp nextsym))
    (without-interrupts
     (if (standard-generic-function-p def)
       (if (and (combined-method-p newdef)
                (eq '%%call-encapsulated-gf (function-name (%combined-method-dcode newdef))))
         (let* ((orig-decode (require-type (cdr (%combined-method-methods newdef)) 'function))
                #+ppc-clos
                (proto (cdr (assq orig-decode dcode-proto-alist)))
                ) ; <<
           (setf (%gf-dcode def) orig-decode)
           #+ppc-clos
           (setf (uvref def 0)(uvref (or proto *gf-proto*) 0)))
         (setf (car (%combined-method-methods (%gf-dcode def))) newdef))
       (typecase spec
         (symbol (%fhave spec newdef))
         (method (setf (%method-function spec) newdef)
                 (remove-obsoleted-combined-methods spec)
                 newdef)))
     (put-encapsulation spec
                        (if (null dont-replace)
                          (function-encapsulation nextsym)))
     (put-encapsulation nextsym nil)
     (unrecord-encapsulation capsule)
     (when (eq (encapsulation-advice-when capsule) :METER) ; SVS. Ensure this table gets cleaned out too.
       (remhash (encapsulation-spec capsule) *metering-table*))
     )))
)

#|
New overhead strategy.
Any given function must:

Keep track of its own overhead, defined as the difference
of its overall time minus its delta-time, where delta-time
is the time taken by just its "meat".
Call this "my-overhead." Add that to *total-overhead* at the END
of the function.

Of course delta-time includes the overhead of CALLED metered
functions too, but we don't care about this, because we will
have already subtracted out ALL of delta-time in our overhead
calculations. (The called metered functions will have appropriately
incremented *total-overhead* themselves, by the time we get
to the end of ourself.)

Note that we do NOT need to remove overhead of CALLED metered functions
in our own calculations, because we assume *total-time* will have been properly
updated by our callees to NOT include their own overhead.

To make this assumption true, we back out our own overhead from our own
updating of *total-time* and thus the assumption becomes true by induction.

We really need to do all the above for consing-overhead too, but that will come later.
|#

#|
Note about atomic-incf and atomic-decf below.
If a given function is being metered in more than one thread simultaneously, it's important to increment and decrement
metering counts atomically. Otherwise, incorrect counts can result.

 It would be even better to lock the entire stats structure during the execution of meter-global-def,
but that would require a lock and waiting for locks inside metering code seems like a very bad idea.
In most metering scenarios, a lack of consistency between elements of a given stats struct is probably not a big deal, because
you shouldn't be checking a given stats structure until all metering uses of it are done and you're reporting the results. By
that time, the structure will be self-consistent again.

It's still likely that *total-time* and overhead calculations will be bogus here when calls in multiple threads are being metered.
|#

; Only svn versions 16532 and later have atomic-incf functions fixed to work with structure refs
(eval-when (:compile-toplevel :load-toplevel :execute)
  (when (>= (parse-integer ccl::*openmcl-svn-revision* :junk-allowed t) 16532)
      (pushnew :atomicity *features*)))
      
#-atomicity ; counts could be slightly inaccurate or inconsistent here because we can't use atomic operations
(defun meter-global-def (function-spec def &optional method-p)
  (let ((stats (make-metering)))
    (setf (get-metering-stats function-spec) stats)
    (macrolet ((initial-lets (&body body)
                 ; would be nice if this could be atomic
                 `(let (;(overhead-start-time (get-time)) ;assume this is close enough to start-time to just use that
                        (prev-total-overhead *total-overhead*)
                        (prev-total-time *total-time*)
                        (prev-total-cons *total-cons*)
                        (prev-total-calls *total-calls*)
                        (start-time (get-time))
                        (start-gctime (get-gctime))
                        (start-cons (get-cons)))
                    (declare (type unsigned-byte prev-total-time)
                             (type unsigned-byte start-time)
                             (type unsigned-byte prev-total-cons)
                             (type unsigned-byte start-cons)
                             (fixnum prev-total-calls))
                    ,@body))
               (post-tally ()
                 ; would be nice if this could be atomic
                 `(let ((delta-time (- (get-time) start-time (- (get-gctime) start-gctime)))
                        (delta-cons (- (get-cons) start-cons))
                        (metered-callee-time (- prev-total-time *total-time*)) ; always negative or 0
                        (metered-callee-cons (- prev-total-cons *total-cons*)) ; always negative or 0
                        )
                    ;(format t "~%Delta-time: ~D" delta-time)
                    ;(format t "~%Metered-callee-time: ~D" metered-callee-time)
                    ; delta-time is the total elapsed time taken by body, which of course includes any time
                    ;   taken by metered functions this body calls. Likewise with delta-cons.
                    ;; Calls
                    (incf (metering-calls stats))
                    (incf *total-calls*)
                    ;;; nested-calls includes this call
                    (incf (metering-nested-calls stats) (the fixnum 
                                                             (- *total-calls*
                                                                prev-total-calls)))
                    ;; Time
                    ;;; Problem with inclusive time is that it
                    ;;; currently doesn't add values from recursive
                    ;;; calls to the same function. Change the
                    ;;; setf to an incf to fix this?
                    (incf (metering-inclusive-time stats) (the unsigned-byte delta-time))
                    ;; At this point, *total-time* may be greater than prev-total-time, because
                    ;;   it will have been incremented by any functions body calls. Must back that
                    ;;   part out to accurately measure exclusive time.
                    ;; Note that there's no way the increment here can be negative; delta-time
                    ;;   MUST be greater than (- prev-total-time *total-time*) because everything measures
                    ;;   total elapsed time. (Okay, it could be negative if a called
                    ;;   metered function executes on a separate core.)
                    (incf (metering-exclusive-time stats) (the unsigned-byte
                                                               (+ delta-time
                                                                  metered-callee-time
                                                                  )))
                    
                    ; this is correct. If you just incremented *total-time*, the time of this body
                    ;   and the time taken by metered functions it calls would be counted twice.
                    (setf *total-time* (the unsigned-byte
                                            (+ prev-total-time delta-time)))
                    
                    ;; Consing
                    (incf (metering-inclusive-cons stats) (the unsigned-byte delta-cons))
                    ;; Similar story as above for exclusive consing
                    (incf (metering-exclusive-cons stats) (the unsigned-byte 
                                                               (+ delta-cons
                                                                  metered-callee-cons)))
                    (setf *total-cons* (the unsigned-byte 
                                            (+ prev-total-cons delta-cons)))
                    
                    ; by this time*, assume *total-overhead* has accurately accumulated the overhead of
                    ;   metered functions called from body. Now we just have to add our own local overhead.
                    ; *actually, by the time body has finished.
                    (let ((my-overhead (the unsigned-byte
                                            (- (get-time) 
                                               start-time ; overall delta time for me and my local overhead
                                               (- (get-gctime) start-gctime) ; any gc time that happened since last get-gctime
                                               delta-time ; subtract out the non-overhead
                                               ))))
                      
                      (incf *total-overhead* my-overhead)
                      ; correct *total-time* to back out my overhead
                      (decf *total-time* my-overhead)))))
      (if method-p
          (lambda (&method saved-method &rest arglist)
            (declare (dynamic-extent arglist))
            (initial-lets
             (multiple-value-prog1 (apply-with-method-context saved-method
                                                              (symbol-function def)
                                                              arglist)
               (post-tally))))
          (lambda (&rest arglist)
            (declare (dynamic-extent arglist))
            (initial-lets
             (multiple-value-prog1 (apply (symbol-function def) arglist)
               (post-tally))
             ))))))

#+atomicity
(defun meter-global-def (function-spec def &optional method-p)
  (let ((stats (make-metering)))
    (setf (get-metering-stats function-spec) stats)
    (macrolet ((initial-lets (&body body)
                 ; would be nice if this could be atomic
                 `(let (;(overhead-start-time (get-time)) ;assume this is close enough to start-time to just use that
                        (prev-total-overhead *total-overhead*)
                        (prev-total-time *total-time*)
                        (prev-total-cons *total-cons*)
                        (prev-total-calls *total-calls*)
                        (start-time (get-time))
                        (start-gctime (get-gctime))
                        (start-cons (get-cons)))
                    (declare (type unsigned-byte prev-total-time)
                             (type unsigned-byte start-time)
                             (type unsigned-byte prev-total-cons)
                             (type unsigned-byte start-cons)
                             (fixnum prev-total-calls))
                    ,@body))
               (post-tally ()
                 ; would be nice if this could be atomic
                 `(let ((delta-time (- (get-time) start-time (- (get-gctime) start-gctime)))
                        (delta-cons (- (get-cons) start-cons))
                        (metered-callee-time (- prev-total-time *total-time*)) ; always negative or 0
                        (metered-callee-cons (- prev-total-cons *total-cons*)) ; always negative or 0
                        )
                    ;(format t "~%Delta-time: ~D" delta-time)
                    ;(format t "~%Metered-callee-time: ~D" metered-callee-time)
                    ; delta-time is the total elapsed time taken by body, which of course includes any time
                    ;   taken by metered functions this body calls. Likewise with delta-cons.
                    ;; Calls
                    (atomic-incf (metering-calls stats))
                    (atomic-incf *total-calls*)
                    ;;; nested-calls includes this call
                    (atomic-incf-decf (metering-nested-calls stats) (the fixnum 
                                                             (- *total-calls*
                                                                prev-total-calls)))
                    ;; Time
                    ;;; Problem with inclusive time is that it
                    ;;; currently doesn't add values from recursive
                    ;;; calls to the same function. Change the
                    ;;; setf to an incf to fix this?
                    (atomic-incf-decf (metering-inclusive-time stats) (the unsigned-byte delta-time))
                    ;; At this point, *total-time* may be greater than prev-total-time, because
                    ;;   it will have been incremented by any functions body calls. Must back that
                    ;;   part out to accurately measure exclusive time.
                    ;; Note that there's no way the increment here can be negative; delta-time
                    ;;   MUST be greater than (- prev-total-time *total-time*) because everything measures
                    ;;   total elapsed time. (Okay, it could be negative if a called
                    ;;   metered function executes on a separate core.)
                    (atomic-incf-decf (metering-exclusive-time stats) (the unsigned-byte
                                                               (+ delta-time
                                                                  metered-callee-time
                                                                  )))
                    
                    ; this is correct. If you just incremented *total-time*, the time of this body
                    ;   and the time taken by metered functions it calls would be counted twice.
                    (setf *total-time* (the unsigned-byte
                                            (+ prev-total-time delta-time)))
                    
                    ;; Consing
                    (atomic-incf-decf (metering-inclusive-cons stats) (the unsigned-byte delta-cons))
                    ;; Similar story as above for exclusive consing
                    (atomic-incf-decf (metering-exclusive-cons stats) (the unsigned-byte 
                                                               (+ delta-cons
                                                                  metered-callee-cons)))
                    (setf *total-cons* (the unsigned-byte 
                                            (+ prev-total-cons delta-cons)))
                    
                    ; by this time*, assume *total-overhead* has accurately accumulated the overhead of
                    ;   metered functions called from body. Now we just have to add our own local overhead.
                    ; *actually, by the time body has finished.
                    (let ((my-overhead (the unsigned-byte
                                            (- (get-time) 
                                               start-time ; overall delta time for me and my local overhead
                                               (- (get-gctime) start-gctime) ; any gc time that happened since last get-gctime
                                               delta-time ; subtract out the non-overhead
                                               ))))
                      
                      (atomic-incf-decf *total-overhead* my-overhead)
                      ; correct *total-time* to back out my overhead
                      (atomic-incf-decf *total-time* (- my-overhead))))))
      (if method-p
          (lambda (&method saved-method &rest arglist)
            (declare (dynamic-extent arglist))
            (initial-lets
             (multiple-value-prog1 (apply-with-method-context saved-method
                                                              (symbol-function def)
                                                              arglist)
               (post-tally))))
          (lambda (&rest arglist)
            (declare (dynamic-extent arglist))
            (initial-lets
             (multiple-value-prog1 (apply (symbol-function def) arglist)
               (post-tally))
             ))))))
 
(defun reset-metering-info (spec)
  (%reset-metering-info (get-metering-stats spec)))

(defun %reset-metering-info (stats)
  (setf (metering-inclusive-time stats) 0)
  (setf (metering-inclusive-cons stats) 0)
  (setf (metering-exclusive-time stats) 0)
  (setf (metering-exclusive-cons stats) 0)
  (setf (metering-calls stats) 0)
  (setf (metering-nested-calls stats) 0))
  
(defun reset-all-metering () 
  "Reset metering info for all functions."
  (setf *total-time* 0
        *total-cons* 0
        *total-calls* 0
        *total-overhead* 0)
  (maphash #'(lambda (spec stats)
               (declare (ignore spec))
               (%reset-metering-info stats))
           *metering-table*))

(defun metered-functions ()
  (let ((result '()))
    (maphash #'(lambda (key value)
                 (declare (ignore value))
                 (push key result))
             *metering-table*)
    result))

(defun meter (function &key define-if-not)
  "Accepts same function syntax as advise (except this is a function, not a macro, so you need to quote
    the arg)."
  (let* ((newsym (gensym "METER"))
         ; WAS typep advise-thing 'method
         (method-p (or (typep function 'method) ; can this happen? You bet!
                       (and (consp function)(eq (car function) :method))))
         (newdef (meter-global-def function newsym method-p)))
      (advise-2 newdef newsym method-p function :meter :meter ; when and name are :meter
                 define-if-not)))

#-MCL-COMMON-MOP-SUBSET
(defun pretty-class-name (method-specializer)
  (if (listp method-specializer)
    method-specializer
    (class-name method-specializer)))


#-MCL
(defun uncanonicalize-specializer (specializer)
  (etypecase specializer
    (class (class-name specializer))
    (eql-specializer (list 'eql (eql-specializer-object specializer)))))

#+MCL-COMMON-MOP-SUBSET
(defun pretty-class-name (method-specializer)
  (uncanonicalize-specializer method-specializer))

(defun prettify-method (method)
  "Returns a list of the form (:method ...) which is suitable for input to advice, trace, or meter."
  `(:method ,(method-name method)
            ,@(method-qualifiers method)
            ,(mapcar 'pretty-class-name (method-specializers method))
            ))

(defun get-methods (generic-function)
  (let ((all-methods (generic-function-methods generic-function)))
    #-MCL-COMMON-MOP-SUBSET
    (setf all-methods ; because accessors cannot be encapsulated in pre-MOP MCL
          (remove-if #'(lambda (method)
                         (typep method 'standard-accessor-method))
                     all-methods))
    all-methods))

(defun meter* (function &key define-if-not)
  "Like meter but if function is a GF, it meters all its methods extant at the time and
   does not meter the GF itself."
  (let ((gf nil))
    (if (standard-generic-function-p (setf gf (fboundp function)))
      (let ((results '()))
         (flet ((meterit (x)
                (meter x :define-if-not define-if-not)))
         (dolist (method (get-methods gf))
           (push (meterit (prettify-method method)) results))
         results))
      (meter function :define-if-not define-if-not))))

; (trace ccl::METER-INFO-VALUES) to see if any values being returned are negative

(defun meter-info-values (spec &optional (nested :exclusive))
  "Returns metering information values for the specified function,
   adjusted for overhead."
  (let ((stats (if (typep spec 'metering)
                 spec
                 (get-metering-stats spec))))
    (if stats
      (case nested
        (:exclusive (values (metering-calls stats)
                            (metering-nested-calls stats)
                            
                            #+BOGUS ; too often, this returns a negative number. Bag the whole overhead thing.
                            (- (metering-exclusive-time stats)
                               (* (metering-calls stats) *meter-time-overhead*))
                            #-BOGUS
                            (metering-exclusive-time stats)

                            #+BOGUS ; too often, this returns a negative number. Bag the whole overhead thing.
                            (- (metering-exclusive-cons stats)
                               (* (metering-calls stats) *meter-cons-overhead*))
                            #-BOGUS
                            (metering-exclusive-cons stats)
                            ))
        ;; Nested-calls includes the
        ;; calls of the function as well. [Necessary 'cause of
        ;; functions which call themselves recursively.]
        (:inclusive (values (metering-calls stats)
                            (metering-nested-calls stats)
                            #+BOGUS ; too often, this returns a negative number. Bag the whole overhead thing.
                            (- (metering-inclusive-time stats)
                               (* (metering-nested-calls stats) *meter-time-overhead*))
                            #-BOGUS
                            (metering-inclusive-time stats)

                            #+BOGUS ; too often, this returns a negative number. Bag the whole overhead thing.
                            (- (metering-inclusive-cons stats)
                               (* (metering-nested-calls stats) *meter-cons-overhead*))
                            #-BOGUS
                            (metering-inclusive-cons stats)
                            )))
      (values 0 0 0 0))))

(defun REPORT-METERING (&optional specs
                                  (nested :exclusive) 
                                  (threshold 0.01)
                                  (key :percent-time)
                                  ignore-no-calls)
  "Report the current metering state.
  The percentage of the total time spent executing unmetered code
  in each function (:exclusive mode), or total time (:inclusive mode)
  will be printed together with the number of calls and
  the unmetered time per call.  Functions that have been executed
  below THRESHOLD % of the time will not be reported."
  (when (or (null specs) (eq specs :all))
    (setf specs (metered-functions)))
  ;(format t "Specs are: ~S~%" specs)
  (if (null specs)
    (format *trace-output* "No metered functions.")
    (let ((metering-results nil)
          (total-time 0)
          (total-cons 0)
          (total-calls 0))
      ;; Compute overall time and consing.
      (dolist (spec specs)
        (multiple-value-bind (calls nested-calls time cons)
                             (meter-info-values spec nested)
          (declare (ignore nested-calls))
          (incf total-calls calls)
          (incf total-time time)
          (incf total-cons cons)))
      ;; Total overhead.
      #+ignore
      (setf *estimated-total-overhead*        
            (/ (* *meter-time-overhead* total-calls)
               metering-time-units-per-second))
      (setf *estimated-total-overhead*        
            (/ *total-overhead*
               metering-time-units-per-second))
      ;; Assemble data for only the specified specs (all metered functions)
      (if (zerop total-time)
        (format *trace-output* "Not enough execution time to meter.")
        (progn
          (setf *no-calls* nil)
          (dolist (spec specs)
            (multiple-value-bind (calls nested-calls time cons)
                                 (meter-info-values spec nested)
              (declare (ignore nested-calls))
              (when (minusp time) (setf time 0.0))
              (when (minusp cons) (setf cons 0.0))
              (if (zerop calls)
                (push (if (symbolp spec) 
                        (symbol-name spec)
                        (format nil "~S" spec))
                      *no-calls*)
                (push (make-metering-info
                       (format nil "~S" spec) ; name
                       calls          ; calls
                       (/ time (float metering-time-units-per-second)) ; time in secs
                       (round cons)   ; consing
                       (/ time (float total-time)) ; percent-time
                       (if (zerop total-cons) 0
                         (/ cons (float total-cons))) ; percent-cons
                       (/ (/ time (float calls)) ; time-per-call
                          metering-time-units-per-second) ; sec/call
                       (round (/ cons (float calls)))) ; cons-per-call
                      metering-results))))
          (display-metering-results metering-results threshold key ignore-no-calls))))))

(defun METER-ALL (&optional (package *package*))
  "Meter all functions in the specified package."
  (let ((package (if (symbolp package)
                     (find-package package)
                     package)))
    (do-symbols (symbol package)
      (when (and (eq (symbol-package symbol) package)
                 (fboundp symbol)
                 (not (macro-function symbol)))
        (meter* symbol)))))

(defmacro METER-FORM (form
                        &optional (nested :exclusive) (threshold 0.01)
                        (key :percent-time))
  "Meter the execution of all functions in the current package
   during the execution of FORM.  All functions that are executed above
   THRESHOLD % will be reported."
  `(unwind-protect
     (progn
       (meter-all)
       (reset-all-metering)
       (multiple-value-prog1
         (time ,form)
         (report-metering :all ,nested ,threshold ,key :ignore-no-calls)))
     (unmeter t)))

(defmacro WITH-METERING* ((&rest functions)
                            (&optional (nested :exclusive) 
                                       (threshold 0.00)
                                       (key :percent-time))
                            &body body)
  "Meter the specified functions during the execution of the body.
   Generic functions will have all their methods individually metered.
   Key parameter affects which column results are sorted in. It should be one of
   :percent-time, :function [sorts by function name], :percent-cons,
   :time-per-call, or :cons-per-call."
  `(unwind-protect
     (progn
       (dolist (fun ',functions)
         (meter* fun))
       (reset-all-metering)
       (multiple-value-prog1
         ,@body
         (report-metering :all ,nested ,threshold ,key)))
     (unmeter t)
     ))

(defmacro WITH-METERING ((&rest functions)
                            (&optional (nested :exclusive) 
                                       (threshold 0.01)
                                       (key :percent-time))
                            &body body)
  "Meter the specified functions during the execution of the body.
   Does NOT meter generic functions specially.
   Key parameter affects which column results are sorted in. It should be one of
   :percent-time, :function [sorts by function name], :percent-cons,
   :time-per-call, or :cons-per-call."
  `(unwind-protect
     (progn
       (dolist (fun ',functions)
         (meter fun))
       (reset-all-metering)
       (multiple-value-prog1
         ,@body
         (report-metering :all ,nested ,threshold ,key)))
     (unmeter t)))


;;; ********************************
;;; Overhead Calculations **********
;;; ********************************
(defparameter overhead-iterations2 100000
  "Number of iterations over which the timing overhead is averaged.")

(proclaim '(notinline stub-function))
(defun STUB-FUNCTION (x)
  (declare (integer x) (optimize (safety 3) (speed 0) (debug 3)))
  (* x (+ x (random (1+ x)))))

(defun set-meter-overhead ()
  "Determines the average overhead of metering by metering the execution
  of an empty function many times." 
  (flet ((run-stub ()
           (without-interrupts
             (dotimes (x overhead-iterations2)
               (stub-function (random 100))) ; hope this will prevent the compiler from omitting this loop
             )))
    (let ((unmetered-time (get-time))
          (metered-time nil))
      (run-stub)
      (setf unmetered-time (- (get-time) unmetered-time))
      (setf *meter-time-overhead* 0
            *meter-cons-overhead* 0)
      (stub-function 10)
      (meter 'stub-function)
      (reset-all-metering)
      (setf metered-time (get-time))
      (run-stub)
      (setf metered-time (- (get-time) metered-time))
      (let ((fiter (float overhead-iterations2)))
        (multiple-value-bind (calls nested-calls time cons)
                             (meter-info-values 'stub-function)
          (declare (ignore nested-calls))
          (unless (= calls overhead-iterations2)
            (error "Something's wrong. Is it possible that another thread is running #'set-meter-overhead?"))
          (format t "~%Unmetered-time: ~S" unmetered-time)
          (format t "~%Time measured by advise: ~S. Time measured crudely: ~S." time metered-time)
          (setf *meter-time-overhead* ;(/ (- metered-time unmetered-time) fiter) ; wrong.
                (/ time fiter) ; yes, this IS the correct way to do this. Just accounts for what metering infrastructure thinks time is vs what it is without metering infrastructure
                *meter-cons-overhead* (/ cons fiter)))
        (unmeter 'stub-function)
        *meter-time-overhead*))))

#+IGNORE ; no longer using *meter-time-overhead*
(eval-when (:load-toplevel :execute)
  (set-meter-overhead))

(defun sort-results (metering-results &optional (key :percent-time))
  (case key
    (:function             (stable-sort metering-results #'string>
                                 :key #'m-info-name))
    ((:percent-time :time) (stable-sort metering-results #'>
                                 :key #'m-info-time))
    ((:percent-cons :cons) (stable-sort metering-results #'>
                                 :key #'m-info-cons))
    (:calls                (stable-sort metering-results #'>
                                 :key #'m-info-calls))
    (:time-per-call        (stable-sort metering-results #'> 
                                 :key #'m-info-time-per-call))
    (:cons-per-call        (stable-sort metering-results #'>
                                 :key #'m-info-cons-per-call))))

(defun display-metering-results (metering-results &optional (threshold 0.01) (key :percent-time)
                                           (ignore-no-calls t))
  (let* ((filter (lambda (result)
                   (or (zerop threshold)
                       (> (m-info-percent-time result) threshold))))
         (column-instances (loop for column in *metering-columns* collect (make-column-instance :column column))))
    (setf metering-results (sort-results metering-results key))
    (print-column-headers *trace-output* metering-results filter column-instances)
    (dolist (result metering-results)
      (when (funcall filter result)
        (format *trace-output* "~%")
        (print-result *trace-output* result column-instances)
        (loop for ci in column-instances do
          (when (m-column-totalize (column-instance-column ci))
            (setf (column-instance-total ci)
                  (if (eq t (m-column-totalize (column-instance-column ci)))
                    (ignore-errors (+  (if (numberp (column-instance-total ci)) (column-instance-total ci) 0)
                                       (funcall (m-column-value-getter (column-instance-column ci)) result)))
                    (m-column-totalize (column-instance-column ci))))))))
    (format *trace-output* "~%")
    (print-column-trailers *trace-output* column-instances)
    (format *trace-output*
            "~%Estimated total metering overhead: ~F seconds"
            *estimated-total-overhead*)
    (when (and (not ignore-no-calls) *no-calls*)
      (setf *no-calls* (sort *no-calls* #'string<))
      (let ((num-no-calls (length *no-calls*)))
        (if (> num-no-calls 20)
          (format *trace-output*
                  "~%~@(~r~) metered functions were not called. ~
            ~%See the variable ccl::*no-calls* for a list."
                  num-no-calls)
          (format *trace-output*
                  "~%The following metered functions were not called:~
            ~%~{~<~%~:; ~A~>~}~%"
                  *no-calls*))))
    (values)))

;;; EXAMPLES
#|
#-MCL
(with-metering (directory %path-cat %path-std-quotes  %unix-file-kind  ftd-ff-call-expand-function
                           %ff-call  get-foreign-namestring  %read-dir  %new-directory-p  %open-dir
                           %file*= %split-dir  %add-directory-result  %all-directories %stat
                           %directory %files-in-directory %some-specific %one-wild %process-directory-result)
                          (:exclusive 0.0)
                          (length (directory "ccl:**;*" :files t :directories nil :follow-links nil :include-emacs-lockfiles t)))

#+MCL
(with-metering (directory %directory2 %path-std-quotes 
                          path-to-fsref
                          %all-directories2
                          %split-dir
                          maybe-resolve-alias
                          get-fsref-name-tail-ustr
                          does-pattern-match-ustr
                          %dir-sub-dir2
                          %dir-sub-file2
                          string-from-hfsunistr
                          quote-some-chars-in-hfsunistr
                          do-name-and-type-match-ustr
                          %files-in-directory2 %some-specific2 %one-wild2)
                          (:exclusive 0.0)
                          (length (directory "ccl:**;*" :files t :directories nil)))
|#