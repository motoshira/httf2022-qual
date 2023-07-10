(in-package #:cl-user)

;;;
;;; Init
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  #+swank (declaim (optimize (speed 3) (safety 2)))
  #-swank (declaim (optimize (speed 3) (safety 0) (debug 0)))
  #-swank (declaim (sb-ext:muffle-conditions sb-ext:compiler-note))
  #-swank (sb-ext:disable-debugger))

;;;
;;; Reader Macros
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  (set-dispatch-macro-character
   #\# #\f
   #'(lambda (stream c2 n)
       (declare (ignore c2 n))
       (let ((form (read stream t nil t)))
         `(lambda (&optional %) (declare (ignorable %)) ,form))))

  (set-dispatch-macro-character
   #\# #\>
   #'(lambda (stream c2 n)
       (declare (ignore c2 n))
       (let ((form (read stream t nil t)))
         (declare (ignorable form))
         #-swank nil
         #+swank (if (atom form)
                     `(format *error-output* "~a => ~a~&" ',form ,form)
                     `(format *error-output* "~a => ~a~&" ',form `(,,@form)))))))

;;;
;;; Libraries
;;;

;;;
;;; Macros
;;;

(in-package #:cl-user)

(defmacro do-iota ((var count &optional (start 0) (step 1)) &body body)
  (check-type step integer)
  (let* ((last (gensym))
         (terminate (if (plusp step) `(>= ,var ,last) `(<= ,var ,last))))
    `(let ((,last (+ ,start (the fixnum (* ,step ,count)))))
       (declare (fixnum ,last))
       (do
        ((,var ,start (+ ,var ,step)))
        (,terminate) (progn ,@body)))))

(defmacro awhen (test &body forms)
  `(let ((it ,test))
     (when it
       ,@forms)))

(defmacro while (test &body body)
  `(loop while ,test do (progn ,@body)))

(defmacro eval-always (&body body)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,@body))

;;;
;;; I/O
;;;

(in-package #:cl-user)

(declaim (inline println))
(defun println (obj &optional (stream *standard-output*))
  #+sbcl (declare (sb-kernel:ansi-stream stream))
  (let ((*read-default-float-format* 'double-float))
    (prog1 obj
      (princ obj stream)
      (terpri stream))))

(declaim (inline %read-byte))
(defun %read-byte (&optional (stream *standard-input*))
  (declare (inline read-byte)
           #+(and sbcl (not swank)) (sb-kernel:ansi-stream stream))
  (the fixnum #+swank (char-code (read-char stream nil #\Nul))
              #-swank (read-byte stream nil #.(char-code #\Nul))))

(declaim (inline read-fixnum))
(defun read-fixnum (&optional (in *standard-input*) (byte-reader #'%read-byte))
  ;; Ref: https://competitive12.blogspot.com/2020/03/common-lisp.html
  ;;        partially modified
  (declare ((function (stream) (unsigned-byte 8)) byte-reader)
           (optimize (speed 3) (safety 0) (debug 0)))
  (let ((minus nil)
        (res 0))
    (declare (boolean minus)
             (fixnum res))
    (labels ((%byte->num (b)
               (the fixnum (- (the fixnum b) #.(char-code #\0))))
             (%digit-p (byte)
               (<= #.(char-code #\0) (the fixnum byte) #.(char-code #\9)))
             (%first-proc! ()
               (loop for byte of-type fixnum = (funcall byte-reader in)
                     do (cond
                          ((%digit-p byte)
                           (setf (the fixnum res) (%byte->num byte))
                           (return))
                          ((= byte #.(char-code #\Nul))
                           (error "EOF"))
                          ((= byte #.(char-code #\-))
                           (setf minus t)))))
             (%rest-proc! ()
               (loop for byte of-type fixnum = (funcall byte-reader in)
                     do (cond
                          ((%digit-p byte)
                           (setf (the fixnum res) (the fixnum (+ (the fixnum (* res 10)) (%byte->num byte)))))
                          (t (return))))))
      (declare (inline %byte->num %digit-p %first-proc! %rest-proc!))
      (%first-proc!)
      (%rest-proc!)
      (the fixnum (if minus (- res) res)))))

(declaim (inline read-base-char))
(defun read-base-char (&optional (stream *standard-input*))
  (code-char (%read-byte stream)))

(defun read-line-fast (&optional (stream *standard-input*))
  #+(and (not swank) sbcl) (declare (sb-kernel:ansi-stream stream))
  (loop with buffer of-type base-string = (make-array 0 :element-type 'base-char :fill-pointer 0)
        for c of-type base-char = (read-base-char stream)
        until (or (eql c #\Newline)
                  (eql c #\Nul))
        do (vector-push-extend c buffer)
        finally (return buffer)))

(declaim (inline parse-fixnum))
(defun parse-fixnum (string)
  (with-input-from-string (in string)
    (read-fixnum in #f(the (unsigned-byte 8)
                           (char-code (read-char % nil #\Nul nil))))))

(declaim (inline read-times))
(defun read-times (count &key (result-type 'list) (reader #'read-fixnum))
  (coerce (loop repeat count collect (funcall reader)) result-type))

;;;
;;; Body
;;;

(in-package #:cl-user)

(defstruct (input (:conc-name in-))
  (member-amount nil :type fixnum)
  (task-factors nil :type (simple-array fixnum (* *)))
  (relations-by-task-id nil :type simple-vector))

(defun task-amount (input)
  (array-dimension (in-task-factors input) 0))

(defun factor-amount (input)
  (array-dimension (in-task-factors input) 1))

(defun dependent-task-ids-by-task-id (input task-id)
  (aref (in-relations-by-task-id input) task-id))

(defun read-input ()
  (let* ((n (read))
         (m (read))
         (k (read))
         (r (read))
         (ds (make-array (list n k) :element-type 'fixnum))
         (es (make-array n :element-type 'list
                           :initial-element nil)))
    (dotimes (i n)
      (dotimes (j k)
        (setf (aref ds i j) (read-fixnum))))
    (dotimes (_ r)
      (let ((u (1- (read-fixnum)))
            (v (1- (read-fixnum))))
        (push u (aref es v))))
    (make-input :member-amount m
                :task-factors ds
                :relations-by-task-id es)))

(defstruct (state (:conc-name st-)))

(defclass components ()
  ((state :type state)
   (match-worker-and-task :type function
                          :reader metch-worker-and-task
                          :initarg :mwat)
   (update-worker-factors :type function
                          :reader update-worker-factors
                          :initarg :uwf)
   (treat-done-tasks :type function
                     :reader treat-done-tasks
                     :initarg :tdt)
   (treat-assign :type function
                 :reader treat-assign
                 :initarg :ta)))

(defun main ()
  (let ((n (parse-fixnum
            (read-line-fast))))
    (println n)))

#-swank (main)

;;;
;;; Debug
;;;

#+swank
(defun run ()
  (let ((*standard-input*
          (make-string-input-stream
           (with-output-to-string (*standard-output*)
             (run-program
              (truename "~/.roswell/bin/copy-or-paste")
              '()
              :output *standard-output*)))))
    (main)))

;; Raise error on warning at compile time

#+(and sbcl (not swank))
(eval-when (:compile-toplevel)
  (when (or (plusp sb-c::*compiler-warning-count*)
            sb-c::*undefined-warnings*)
    (error "compiler-error-count:~a, undefined warnings:~a"
           sb-c::*compiler-warning-count*
           sb-c::*undefined-warnings*)))

#+swank
(defun run-sample (infile outfile &optional (out *standard-output*))
  (with-open-file (*standard-input* infile :direction :input)
    (with-open-file (*standard-output* outfile :direction :output
                                               :if-exists :supersede)
      (main))
    (sb-ext:run-program "target/release/vis" (list infile outfile)
                        :search t
                        :output out
                        :error *error-output*)))

#+swank
(defun show-vis ()
  (sb-ext:run-program "google-chrome" '("vis.html")
                      :search t))