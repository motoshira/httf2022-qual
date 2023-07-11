(in-package #:cl-user)

;;;
;;; Init
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  #+swank (declaim (optimize (speed 3) (safety 2)))
  ;; #-swank (declaim (optimize (speed 3) (safety 0) (debug 0)))
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

(defconstant +inf+ #.(expt 10 18))

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

(defun read-done-worker-ids ()
  (let ((cnt (read)))
    (when (>= cnt 0)
      (values (loop repeat cnt
                    collect (1- (read-fixnum)))
              t))))

;; VO

(defstruct (task-worker-pair (:conc-name twp-))
  (task-id nil :type fixnum)
  (worker-id nil :type fixnum))

;; entity repository

(defstruct worker
  (id nil :type fixnum)
  (assigned-task-id nil :type (or null fixnum))
  (factors nil :type (simple-array fixnum (*))))

(defgeneric find-worker-by-id (state worker-id))
(defgeneric update-worker-factors-by-id (state worker-id factors)
  (:documentation "factorsは(simple-array fixnum (*))"))
(defgeneric find-unassigned-workers (state))

(defstruct task
  (id nil :type fixnum :read-only t)
  (assigned-member-id nil :type (or null fixnum))
  (done nil :type boolean)
  (dependent-task-ids nil :type list :read-only t)
  (factors nil :type (simple-array fixnum (*))))

(defgeneric find-task-by-id (state task-id))
(defgeneric find-undone-and-unassigned-tasks (state)
  (:documentation "誰かがassignされているタスクは含まない"))

;; service

(defgeneric make-task-done (state task-id)
  (:documentation "workerも解放する"))
(defgeneric assign-task (state task-id worker-id)
  (:documentation "いずれもfreeであることを期待する"))
;; (defgeneric find-assigned-task-worker-pairs (state))

;; usecase

(defgeneric match-worker-and-task (matcher components input))
(defgeneric update-worker-factors (updater components input pairs))
(defgeneric handle-done-tasks (handler components input done-worker-ids))
(defgeneric handle-assign (handler components input pairs))

(defclass components ()
  ((state :reader state
          :initarg :state)
   (worker-and-task-matcher :reader worker-and-task-matcher
                            :initarg :watm)
   (worker-factors-updater :reader worker-factors-updater
                           :initarg :wfu)
   (done-tasks-handler :reader done-tasks-handler
                       :initarg :dth)
   (assign-handler :reader assign-handler
                   :initarg :ah)))

(defun game-loop (components input)
  ;; TODO validation
  (with-accessors ((watm worker-and-task-matcher)
                   (ah assign-handler)
                   (dth done-tasks-handler)
                   (wfu worker-factors-updater)) components
    (loop for day from 1 do
      (let ((pairs (match-worker-and-task watm components input)))
        (format t
                "~a ~{~a~^ ~}~%"
                (length pairs)
                (loop for pair in pairs
                      append (list (1+ (twp-worker-id pair))
                                   (1+ (twp-task-id pair)))))
        (finish-output)
        (handle-assign ah components input pairs)
        (multiple-value-bind (done-worker-ids more) (read-done-worker-ids)
          ;; 終了
          (unless more
            (println "end" *error-output*)
            (return))
          (format *error-output* "day~a done-worker-ids:~a~&" day done-worker-ids)
          (handle-done-tasks dth components input done-worker-ids)
          (update-worker-factors wfu components input pairs))))))

;;
;; impl
;;

;; matcher
;; TODO minCostFlow

(defstruct (greedy-matcher (:conc-name gm-))
  ;; list of functions
  (evaluators nil :type list))

#+nil
(defun %estimated-cost (worker task)
  (loop for task-factor across (task-factors task)
        for worker-factor across (worker-factors worker)
        sum (max 0 (the fixnum
                        (- task-factor worker-factor)))))

(defun %estimated-cost (gm worker task)
  (the fixnum
       (loop for fn in (gm-evaluators gm)
             sum (the fixnum (funcall fn worker task)))))

(defmethod match-worker-and-task ((gm greedy-matcher) components input)
  ;; TODO selectableかどうかの判定を別のところに切り出す
  ;; TODO 評価でやってしまったほうがシンプルでいい気もする
  (with-accessors ((state state)) components
    (with-accessors ((evaluator gm-evaluator)) gm
      (let ((res nil)
            (workers (find-unassigned-workers state))
            (tasks (find-undone-and-unassigned-tasks state))
            (assigned-task-ids (make-hash-table)))
        (dolist (worker workers)
          (let ((min-cost +inf+)
                (task-id -1))
            (dolist (task tasks)
              (let ((dependent-task-ids (task-dependent-task-ids task)))
                (when (and (not (gethash (task-id task) assigned-task-ids))
                           (loop for t-id in dependent-task-ids
                                 for tt = (find-task-by-id state t-id)
                                 always (task-done tt)))
                  (let ((est-cost (%estimated-cost gm worker task)))
                    (when (< est-cost min-cost)
                      (setf min-cost est-cost
                            task-id (task-id task)))))))
            (when (>= task-id 0)
              (push (make-task-worker-pair :task-id task-id
                                           :worker-id (worker-id worker))
                    res)
              (setf (gethash task-id assigned-task-ids) t))))
        (nreverse res)))))

;; handler

(defstruct (done-tasks-handler (:conc-name dth-)))

(defmethod handle-done-tasks ((_ done-tasks-handler) components input done-worker-ids)
  (with-accessors ((state state)) components
    (let ((task-ids (loop for worker-id in done-worker-ids
                          for worker = (find-worker-by-id state worker-id)
                          collect (worker-assigned-task-id worker))))
      (format *error-output* "handle-done-task done-worker-ids:~a task-ids:~a~&" done-worker-ids task-ids)
      (dolist (task-id task-ids)
        (make-task-done state task-id)))))

(defstruct (assign-handler (:conc-name ah-)))

(defmethod handle-assign ((_ assign-handler) components input pairs)
  (format *error-output* "handle-assign pairs:~a~&" pairs)
  (with-accessors ((state state)) components
    (dolist (pair pairs)
      (assign-task state (twp-task-id pair) (twp-worker-id pair)))))

;; updater
;; TODO 焼きなまし

(defstruct (init-updater (:conc-name iu-))
  (unknown-factor nil :type fixnum))

(defstruct (no-means-updater (:conc-name nmu-)
                             (:constructor make-no-means-updater (unknown-factor)))
  "何もしない"
  (iu (make-init-updater :unknown-factor unknown-factor) :type init-updater)
  (init nil :type boolean))

;; TODOcompined updater

(defmethod update-worker-factors ((iu init-updater) components input pairs)
  (with-accessors ((state state)) components
    (dolist (pair pairs)
      (update-worker-factors-by-id state
                                   (twp-worker-id pair)
                                   (coerce
                                    (loop repeat (factor-amount input)
                                          collect (iu-unknown-factor iu))
                                    '(simple-array fixnum (*)))))))

(defmethod update-worker-factors ((nmu no-means-updater) components input pairs)
  (unless (nmu-init nmu)
    ;; delegate
    (update-worker-factors (nmu-iu nmu) components input pairs)
    (setf (nmu-init nmu) t)))

;; state impl

(defstruct (state (:conc-name st-)
                  (:constructor %make-state))
  (workers nil :type (simple-array worker (*)))
  (tasks nil :type (simple-array task (*))))

(defun make-state (input)
  (let ((k (factor-amount input)))
    (%make-state :workers (coerce (loop for i below (in-member-amount input)
                                        collect (make-worker :id i
                                                             :factors (make-array k :element-type 'fixnum)))
                                  '(simple-array worker (*)))
                 :tasks (coerce (loop for i below (task-amount input)
                                      for factors = (coerce
                                                     (loop for j below k
                                                           collect (aref (in-task-factors input) i j))
                                                     '(simple-array fixnum (*)))
                                      collect (make-task :id i
                                                         :factors factors
                                                         :dependent-task-ids (dependent-task-ids-by-task-id input i)))
                                '(simple-array task (*))))))

(defmethod find-worker-by-id ((state state) worker-id)
  (aref (st-workers state) worker-id))

(defmethod update-worker-factors-by-id ((state state) worker-id factors)
  (symbol-macrolet ((worker (find-worker-by-id state worker-id)))
    (setf (worker-factors worker) factors)))

(defmethod find-unassigned-workers ((state state))
  (coerce
   (remove-if #'worker-assigned-task-id (st-workers state))
   'list))

(defmethod find-task-by-id ((state state) task-id)
  (aref (st-tasks state) task-id))

(defmethod find-undone-and-unassigned-tasks ((state state))
  (coerce
   (remove-if #f(or (task-assigned-member-id %)
                    (task-done %))
              (st-tasks state))
   'list))

(defmethod make-task-done ((state state) task-id)
  (let ((worker-id (task-assigned-member-id (find-task-by-id state task-id))))
    (symbol-macrolet ((task (aref (st-tasks state) task-id))
                      (worker (aref (st-workers state) worker-id)))
      (setf (task-assigned-member-id task) nil
            (task-done task) t
            (worker-assigned-task-id worker) nil))))

(defmethod assign-task ((state state) task-id worker-id)
  (symbol-macrolet ((task (find-task-by-id state task-id))
                    (worker (find-worker-by-id state worker-id)))
    (setf (task-assigned-member-id task) worker-id
          (worker-assigned-task-id worker) task-id)))

;; (defmethod find-assigned-task-worker-pairs ((state state))
;;   ())

;; main

(defconstant +unknown-factor+ 100)

(defun make-components (input)
  (make-instance 'components
                 :state (make-state input)
                 :watm (make-greedy-matcher)
                 :wfu (make-no-means-updater +unknown-factor+)
                 :dth (make-done-tasks-handler)
                 :ah (make-assign-handler)))

(defun main ()
  (let* ((input (read-input))
         (components (make-components input)))
    (game-loop components input)))

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
