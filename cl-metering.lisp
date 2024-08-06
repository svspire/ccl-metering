;;; CL-metering.lisp
;;; Shannon Spires 08-Mar-2022

;;; Also see https://gitlab.common-lisp.net/dkochmanski/metering.

;;; Tools for metering lisp functions in CCL, Lispworks, and maybe SBCL (untested in SBCL as yet).

;;; Based on CCL-metering.lisp

;;; This code also has the very useful feature that it enables one to meter individual
;;;   methods of a generic function separately, where MK's does not. (This feature only works in CCL.)
;;;   (Of course, metering regular functions is also still supported).

;;; This operates by essentially wrapping some advice around each metered method or function.
;;; The function #'meter accepts the same syntax as #'advise [in CCL] except it takes fewer args
;;;   since it already knows precisely what extra work it needs to do before and after the nominal
;;;   function.
;;; The function #'meter* works just like #'meter except when you give it a symbol referring to a
;;;   generic function it automatically calls #'meter on all its methods. (This feature only works in CCL.)
;;; The main user interface is #'with-metering or #'with-metering* (CCL only) if you want an individual method breakdown.

;;; This code works better on a 64-bit Common Lisp than 32-bit. If (* 1000000 (get-universal-time)) can't fit into a fixnum, it will have significant overhead.

;;; See examples at the end.

(in-package :cl-user)

(export '(meter unmeter meter* with-metering with-metering* report-metering reset-all-metering
          metered-functions meter-all meter-form))

(defconstant +million+ 1000000)

(defvar *TOTAL-TIME* 0
  "Total amount of time metered so far.")
(defvar *TOTAL-CONS* 0
  "Total amount of consing metered so far.")
(defvar *TOTAL-CALLS* 0
  "Total number of calls metered so far.")
(defvar *TOTAL-CPU-OVERHEAD* 0
  "Total CPU time overhead so far.")
(defvar *TOTAL-CONS-OVERHEAD* 0
  "Total consing overhead so far.")

(defvar *no-calls* nil
  "A list of metered functions that weren't called. This is a global only for reporting convenience; when
   it's too long to display with normal reporting results, the user can inspect the variable.")

(defvar *estimated-total-cpu-overhead* 0 "Estimated metering overhead of CPU time in seconds")

(defvar *metering-table*
  (make-hash-table :test #'equal))

(defparameter metering-time-units-per-second +million+)
(defparameter gc-time-conversion-factor (/ metering-time-units-per-second internal-time-units-per-second))
(defparameter *use-wall-time* nil "True for CPU time; nil if you need wall time")

#+OPENMCL
(defun get-wall-time-usec ()
  "This might or might not be actual wall clock time, but it's guaranteed monotonic. That's all we need."
  (declare (optimize (speed 3) (debug 0)))
  (ccl:rlet ((now :timeval)
         (since :timeval))
    (#_gettimeofday now (ccl:%null-ptr))
    (ccl::%sub-timevals since now ccl::*lisp-start-timeval*)
    (+ (* +million+ (the (unsigned-byte 32) (ccl:pref since :timeval.tv_sec)))
       (the fixnum (ccl:pref since :timeval.tv_usec)))))

;;; From David McClain, who may have gotten it from https://gitlab.common-lisp.net/dkochmanski/metering
#+(AND :LISPWORKS (OR :LINUX :MACOSX))
(PROGN
 (fli:define-foreign-function (_get-time-of-day "gettimeofday" :source)
    ((tsinfo :pointer)
     (tzinfo :pointer))
   :result-type :long)

 (defun get-wall-time-usec ()
   ;; time since midnight Jan 1, 1970, measured in microseconds
   (fli:with-dynamic-foreign-objects ()
	(let ((arr (fli:allocate-dynamic-foreign-object
		:type   '(:unsigned :long)
		:nelems 2
		:fill   0)))
	 (if (zerop (_get-time-of-day arr fli:*null-pointer*))
             (+ (* +million+ (the integer (fli:dereference arr :index 0)))
                (the integer (fli:dereference arr :index 1)))
           (error "Can't perform Posix gettimeofday()"))
	 ))))

#+SBCL
(defmacro get-wall-time-usec ()
  (multiple-value-bind (secs usecs) (sb-ext:get-time-of-day)
    (+ (* +million+ secs) usecs)))

#-CLOZURE ; do nothing with #> sequences
(set-dispatch-macro-character
 #\# #\>
 (lambda (stream char arg)
    (declare (ignore char arg))
      (progn
        (read stream nil nil nil)
        nil)))

#-CLOZURE ; do nothing with #_ sequences
(set-dispatch-macro-character
 #\# #\_
 (lambda (stream char arg)
    (declare (ignore char arg))
      (progn
        (read stream nil nil nil)
        nil)))

; Can't use %internal-run-time because its resolution is dependent on internal-time-units-per-second. This one is not.
#+CLOZURE
(defun %internal-microsecond-run-time ()
  ;; Returns user and system times in microseconds as multiple values. This is strictly CPU time, not wall clock time.
  #-windows-target
  (rlet ((usage :rusage))
    (ccl::%%rusage usage)
    (let* ((user-seconds (pref usage :rusage.ru_utime.tv_sec))
           (system-seconds (pref usage :rusage.ru_stime.tv_sec))
           (user-micros (pref usage :rusage.ru_utime.tv_usec))
           (system-micros (pref usage :rusage.ru_stime.tv_usec)))
      (values (+ (* user-seconds +million+
                 user-micros))
              (+ (* system-seconds +million+)
                 system-micros))))
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

#+CLOZURE
(defun microsecond-run-time ()
  (multiple-value-bind (user sys) (%internal-microsecond-run-time)
    (+ user sys)))

#+IGNORE ;;#+SBCL ;; NDY but this is SBCL's definition of system-internal-run-time
(defun system-internal-run-time ()
    (multiple-value-bind (ignore utime-sec utime-usec stime-sec stime-usec)
        (unix-fast-getrusage rusage_self)
      (declare (ignore ignore)
               (type unsigned-byte utime-sec stime-sec)
               ;; (Classic CMU CL had these (MOD 1000000) instead, but
               ;; at least in Linux 2.2.12, the type doesn't seem to
               ;; be documented anywhere and the observed behavior is
               ;; to sometimes return 1000000 exactly.)
               (type fixnum utime-usec stime-usec))
      (let ((result (+ (* (+ utime-sec stime-sec)
                          internal-time-units-per-second)
                       (floor (+ utime-usec
                                 stime-usec
                                 (floor micro-seconds-per-internal-time-unit 2))
                              micro-seconds-per-internal-time-unit))))
        result)))

#+SBCL
(defun system-internal-microsecond-run-time ()
    (multiple-value-bind (ignore utime-sec utime-usec stime-sec stime-usec)
        (unix-fast-getrusage rusage_self)
      (declare (ignore ignore)
               (type unsigned-byte utime-sec stime-sec)
               ;; (Classic CMU CL had these (MOD 1000000) instead, but
               ;; at least in Linux 2.2.12, the type doesn't seem to
               ;; be documented anywhere and the observed behavior is
               ;; to sometimes return 1000000 exactly.)
               (type fixnum utime-usec stime-usec))
      (let ((result (+ (* (+ utime-sec stime-sec)
                          +million+)
                       (floor (+ utime-usec
                                 stime-usec
                                 (floor micro-seconds-per-internal-time-unit 2))
                              micro-seconds-per-internal-time-unit))))
        result)))

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
  header ; string or list of strings. If the latter, each will be on a separate line.
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
    (etypecase header
      (cons   (reduce 'max header :key 'length))
      (string (length header)))))

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

; #'get-cpu-time returns total CPU runtime (system+user) in microseconds
#+CLOZURE
(defmacro get-cpu-time ()
  `(the unsigned-byte (microsecond-run-time)))

(defmacro get-wall-time () ; wall clock time in case we need it
  `(the unsigned-byte (get-wall-time-usec)))

#|#+LISPWORKS ; note this allocates 25104 bytes per call!!
(defmacro get-cpu-time ()
  `(the unsigned-byte
        (let ((times (system::get-cpu-times)))
          (+ (* +million+ (slot-value times 'system::user-secs))
             (slot-value times 'system::user-micros)
             (* +million+ (slot-value times 'system::system-secs))
             (slot-value times 'system::system-micros)))))
|#  
  
#+LISPWORKS ; this only allocates 992 bytes per call
(defmacro get-cpu-time ()
  ; note that adding declarations makes this cons more!
  `(the unsigned-byte
        (let ((times (system::get-cpu-times)))
          (declare (dynamic-extent times))
          (+ (* +million+ (+ (slot-value times 'system::user-secs)
                           (slot-value times 'system::system-secs)))
             (slot-value times 'system::user-micros)
             (slot-value times 'system::system-micros)))))

#+CLOZURE
(defmacro get-gctime ()
  `(* gc-time-conversion-factor (gctime)) ;;; this is wall clock time
  0
  )

#+LISPWORKS ; only valid after #'hcl::start-gc-timing has been called and before #'hcl::stop-gc-timing has been called.
(defmacro get-gctime ()
  ;;;(truncate (* +million+ (getf (hcl::get-gc-timing) :total))) ;;; NDY this appears to be wall clock time and thus cannot be compared with cpu time
  0)
  

#+CLOZURE
(defmacro get-cons ()
  `(the unsigned-byte (ccl::total-bytes-allocated)))

#|#+LISPWORKS
(defmacro get-cons ()
  (getf (() :TOTAL-ALLOCATED)) ; this conses a lot which kinda defeats the purpose
|#

(defmacro get-microseconds ()
  (if *use-wall-time*
      (get-wall-time)
      (get-cpu-time)))

#+LISPWORKS
(defmacro get-cons ()
  ; This reports numbers that are much too high compared to what #'time reports.
  ;  This is why I write the "bogus" comment in the report when Lispworks is running. Need help from Martin Simmons to figure this out.
  (nth-value 1 (RAW::INTERNAL-ROOM)))

(defun get-metering-stats (spec)
  (gethash spec *metering-table*))

(defun (setf get-metering-stats) (value spec)
  (setf (gethash spec *metering-table*) value))

#+CLOZURE
(defun %unmeter-all ()
  (unadvise t :when :meter :name :meter)
  ; (unadvise t) [without other qualifiers] will remove all metering as well as all other advice
  (clrhash *metering-table*))

#+LISPWORKS
(defun %unmeter-all ()
  (hcl::stop-gc-timing)
  (let ((specs (metered-functions)))
    (dolist (spec specs)
      (lw:remove-advice spec :METER)))
  (clrhash *metering-table*))

#+CLOZURE
(defun unmeter (function)
  "(unmeter t) will remove all metering advice"
  (cond ((neq function t)
         (ccl::%unadvise-1 function :METER :METER))
        (t (%unmeter-all))))

#+LISPWORKS
(defun unmeter (function)
  "(unmeter t) will remove all metering advice"
  (cond ((not (eq function t))
         (lw:remove-advice function :METER))
        (t (%unmeter-all))))

#|
New overhead strategy.
Any given function must:

Keep track of its own overhead, defined as 
its overall time minus its delta-time, where delta-time
is the time taken by just its "meat".
Call this "my-cpu-overhead." Add that to *total-cpu-overhead* at the END
of the function.

Of course delta-time includes the overhead of CALLED metered
functions too, but we don't care about this, because we will
have already subtracted out ALL of delta-time in our overhead
calculations. (The called metered functions will have appropriately
incremented *total-cpu-overhead* themselves, by the time we get
to the end of ourself.)

Note that we do NOT need to remove overhead of CALLED metered functions
in our own calculations, because we assume *total-time* will have been properly
updated by our callees to NOT include their own overhead.

To make this assumption true, we back out our own overhead from our own
updating of *total-time* and thus the assumption becomes true by induction.
UPDATE 03-Jan-2024
Above sentence is wrong. We _must not_ back out "our own overhead" from our own
updating of *total-time* because _it has already been backed out_. When we update
*total-time*, it's merely incremented by delta-time, which itself includes no 
metering overhead (or at least as little overhead as possible). If we explicitly subtract
my-cpu-overhead from *total-time*, we're subtracting overhead _twice_ which can in some
cases make *total-time* become _negative_ at the end of a metered function. At the
very least, this practice will artificially inflate caller time and artificially
decrease callee time.

We also do all the above for consing-overhead.
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
;  Except release 1.11.5 omitted that patch. So test for the functionality itself.

#+CLOZURE
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defstruct (foostruct)
    (slot1 0))
  (let ((foo (make-foostruct)))
    (declare (ignorable foo))
    (ignore-errors
     (macroexpand `(ccl::atomic-incf-decf (foostruct-slot1 foo) 1))
     (pushnew :atomicity *features*))))

#+LISPWORKS
(defmacro apply-with-method-context (&rest args)
  "Do nothing but don't error if this fn is encountered by the compiler."
  )

(defmacro maybe-atomic-incf (place delta)
  #+(and CLOZURE atomicity)
  `(ccl::atomic-incf-decf ,place ,delta)
  #+LISPWORKS
  `(sys:atomic-incf ,place ,delta)
  #-(or (and CLOZURE atomicity) LISPWORKS) ; counts could be slightly inaccurate or inconsistent here because we can't use atomic operations
  `(incf ,place ,delta))

(defun meter-global-def (function-spec def &optional method-p)
  #-CLOZURE (setf method-p nil) ; this feature only works in CCL
  (let ((stats (make-metering)))
    (setf (get-metering-stats function-spec) stats)
    (macrolet ((initial-lets (&body body)
                 ; would be nice if this could be atomic
                 `(let ((prev-total-time *total-time*)
                        (prev-total-cons *total-cons*)
                        (prev-total-calls *total-calls*)
                        (start-time (get-microseconds))
                        (start-gctime (get-gctime))
                        (start-cons (get-cons)))
                    (declare (type unsigned-byte prev-total-time)
                             (type unsigned-byte start-time)
                             (type unsigned-byte prev-total-cons)
                             (type unsigned-byte start-cons)
                             (fixnum prev-total-calls)
                             (dynamic-extent prev-total-time start-time prev-total-cons start-cons prev-total-calls))
                    ,@body))
               (post-tally ()
                 ; would be nice if this could be atomic
                 `(let ((delta-time (- (get-microseconds) start-time (- (get-gctime) start-gctime)))
                        (delta-cons (- (get-cons) start-cons))
                        (metered-callee-time (- prev-total-time *total-time*)) ; always negative or 0
                        (metered-callee-cons (- prev-total-cons *total-cons*)) ; always negative or 0
                        )
                    (declare (dynamic-extent delta-time delta-cons metered-callee-time metered-callee-cons))
                    (when (< delta-time 0) (error "delta-time shouldn't be negative"))
                    ;(format t "~%~S. Delta-time: ~D" function-spec delta-time)
                    ;(format t "~%~S. Metered-callee-time: ~D" function-spec metered-callee-time)
                    ;(format t "~%~S. Delta-cons: ~D" function-spec delta-cons)
                    ;(format t "~%~S. Metered-callee-cons: ~D" function-spec metered-callee-cons)
                    ; delta-time is the total elapsed time taken by body, which of course includes any time
                    ;   taken by metered functions this body calls. Likewise with delta-cons.
                    ;; Calls
                    (maybe-atomic-incf (metering-calls stats) 1)
                    (maybe-atomic-incf *total-calls* 1)
                    ;;; nested-calls includes this call
                    (maybe-atomic-incf (metering-nested-calls stats) (the fixnum 
                                                                          (- *total-calls*
                                                                             prev-total-calls)))
                    ;; Time
                    ;;; Problem with inclusive time is that it
                    ;;; currently doesn't add values from recursive
                    ;;; calls to the same function. Change the
                    ;;; setf to an incf to fix this?
                    (maybe-atomic-incf (metering-inclusive-time stats) (the unsigned-byte delta-time))
                    ;; At this point, *total-time* may be greater than prev-total-time, because
                    ;;   it will have been incremented by any metered functions body calls. (But only the 
                    ;;   _shallowest_ metered functions (in the stack depth sense) will affect the *total-time*
                    ;;   we can see here. Any effects on *total-time* at deeper levels will have been erased
                    ;;   before we can see them in the context of this code you're reading right here.
                    ;;   Anyway we must back that part out to accurately measure exclusive time.
                    ;; Note that there's no way the increment here can be negative; delta-time
                    ;;   MUST be greater than (- prev-total-time *total-time*) because everything measures
                    ;;   total elapsed time. (Okay, it could be negative if a called
                    ;;   metered function executes on a separate core.)
                    (maybe-atomic-incf (metering-exclusive-time stats) (the unsigned-byte
                                                                            (+ delta-time
                                                                               metered-callee-time
                                                                               )))
                    
                    ; this is correct. If you just incremented *total-time*, the time of this body
                    ;   and the time taken by metered functions it calls would be counted twice.
                    (setf *total-time* (the unsigned-byte
                                            (+ prev-total-time delta-time)))
                    (when (< *total-time* 0) (error "*total-time* is negative"))
                    ;; Consing
                    (maybe-atomic-incf (metering-inclusive-cons stats) (the unsigned-byte delta-cons))
                    ;; Similar story as above for exclusive consing
                    (maybe-atomic-incf (metering-exclusive-cons stats) (the unsigned-byte 
                                                                            (+ delta-cons
                                                                               metered-callee-cons)))
                    (setf *total-cons* (the unsigned-byte 
                                            (+ prev-total-cons delta-cons)))
                    
                    ; by this time*, assume *total-cpu-overhead* has accurately accumulated the overhead of
                    ;   metered functions called from body. Now we just have to add our own local overhead.
                    ; *actually, by the time body has finished.
                    (let ((my-cpu-overhead (the unsigned-byte
                                            (- (get-microseconds) 
                                               start-time ; overall delta time for me and my local overhead
                                               (- (get-gctime) start-gctime) ; any gc time that happened since last get-gctime
                                               delta-time ; subtract out the non-overhead
                                               )))
                          (my-cons-overhead (the unsigned-byte
                                                 (- (get-cons)
                                                    start-cons ; overall delta cons for me and my local overhead
                                                    delta-cons)))) ; subtract out the non-overhead
                      ;(when (< my-cpu-overhead 0) (error "My-cpu-overhead is negative."))
                      (maybe-atomic-incf *total-cpu-overhead* my-cpu-overhead)
                      (maybe-atomic-incf *total-cons-overhead* my-cons-overhead)
                      ; correct *total-time* to back out my overhead
                      ;;; NO!!! *total-time* already has overhead backed out. If you do this, you're backing it out a second time.
                      ;(maybe-atomic-incf *total-time* (- my-cpu-overhead))
                    ))))
      (if method-p
          #+CLOZURE
          (lambda (ccl::&method saved-method &rest arglist)
            (declare (dynamic-extent arglist))
            (initial-lets
             (multiple-value-prog1  (ccl::apply-with-method-context saved-method
                                                              (symbol-function def)
                                                              arglist)
               (post-tally))))
          #-CLOZURE
          (error "Can't meter individual methods except in CCL")
          #+CLOZURE
          (lambda (&rest arglist)
            (declare (dynamic-extent arglist))
            (initial-lets
             (multiple-value-prog1 (apply (symbol-function def) arglist)
               (post-tally))))
          #+LISPWORKS
          (lambda (original-fn &rest arglist)
            (declare (dynamic-extent arglist))
            (initial-lets
             (multiple-value-prog1 (apply original-fn arglist)
               (post-tally))))
          ))))
 
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
  #+LISPWORKS (hcl::start-gc-timing :initialize t)
  (setf *total-time* 0
        *total-cons* 0
        *total-calls* 0
        *total-cpu-overhead* 0
        *total-cons-overhead* 0)
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

#+CLOZURE
(defun meter (function &key define-if-not)
  "Accepts same function syntax as advise (except this is a function, not a macro, so you need to quote
    the arg)."
  (let* ((newsym (gensym "METER"))
         ; WAS typep advise-thing 'method
         (method-p (or (typep function 'method) ; can this happen? You bet!
                       (and (consp function)(eq (car function) :method))))
         (newdef (meter-global-def function newsym method-p)))
      (ccl::advise-2 newdef newsym method-p function :meter :meter ; when and name are :meter
                 define-if-not)))


#+LISPWORKS
(defun meter (fnspec)
  (let* ((newdef (meter-global-def fnspec nil nil)))
    (eval `(defadvice (,fnspec :METER :around) (&rest args)
      (apply ,newdef #'lw:call-next-advice args)))))

#+CLOZURE
(defun uncanonicalize-specializer (specializer)
  (etypecase specializer
    (class (class-name specializer))
    (eql-specializer (list 'eql (eql-specializer-object specializer)))))

#+CLOZURE
(defun pretty-class-name (method-specializer)
  (uncanonicalize-specializer method-specializer))

#+CLOZURE
(defun prettify-method (method)
  "Returns a list of the form (:method ...) which is suitable for input to advice, trace, or meter."
  `(:method ,(method-name method)
            ,@(method-qualifiers method)
            ,(mapcar 'pretty-class-name (method-specializers method))
            ))

(defun get-methods (generic-function)
  (generic-function-methods generic-function))

#+CLOZURE
(defun meter* (function &key define-if-not)
  "Like meter but if function is a GF, it meters all its methods extant at the time and
   does not meter the GF itself."
  (let ((gf nil))
    (if (ccl::standard-generic-function-p (setf gf (fboundp function)))
      (let ((results '()))
         (flet ((meterit (x)
                (meter x :define-if-not define-if-not)))
         (dolist (method (get-methods gf))
           (push (meterit (prettify-method method)) results))
         results))
      (meter function :define-if-not define-if-not))))

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
                            (metering-exclusive-time stats)
                            (metering-exclusive-cons stats)
                            ))
        ;; Nested-calls includes the
        ;; calls of the function as well. [Necessary 'cause of
        ;; functions which call themselves recursively.]
        (:inclusive (values (metering-calls stats)
                            (metering-nested-calls stats)
                            (metering-inclusive-time stats)
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
      (setf *estimated-total-cpu-overhead*        
            (/ *total-cpu-overhead*
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

#+CLOZURE ; only works with CCL for now
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
            "~%Estimated total metering CPU overhead: ~F seconds"
            *estimated-total-cpu-overhead*)
    (format *trace-output*
            "~%Estimated total metering cons overhead: ~D bytes"
            *total-cons-overhead*)
    #+LISPWORKS
    (format *trace-output*
            "~%(Note that consing numbers in Lispworks are probably bogus.)")
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
(with-metering (directory ccl::%path-cat ccl::%path-std-quotes  ccl::%unix-file-kind  ccl::ftd-ff-call-expand-function
                           ccl::%ff-call  ccl::get-foreign-namestring  ccl::%read-dir  ccl::%new-directory-p  ccl::%open-dir
                           ccl::%file*= ccl::%split-dir  ccl::%add-directory-result  ccl::%all-directories ccl::%stat
                           ccl::%directory ccl::%files-in-directory ccl::%some-specific ccl::%one-wild ccl::%process-directory-result)
                          (:exclusive 0.0)
                          (length (directory "ccl:**;*" :files t :directories nil :follow-links nil :include-emacs-lockfiles t)))

(let ((*use-wall-time* t))
(with-metering (directory ccl::%path-cat ccl::%path-std-quotes  ccl::%unix-file-kind  ccl::ftd-ff-call-expand-function
                           ccl::%ff-call  ccl::get-foreign-namestring  ccl::%read-dir  ccl::%new-directory-p  ccl::%open-dir
                           ccl::%file*= ccl::%split-dir  ccl::%add-directory-result  ccl::%all-directories ccl::%stat
                           ccl::%directory ccl::%files-in-directory ccl::%some-specific ccl::%one-wild ccl::%process-directory-result)
                          (:exclusive 0.0)
                          (length (directory "ccl:**;*" :files t :directories nil :follow-links nil :include-emacs-lockfiles t))))
|#
