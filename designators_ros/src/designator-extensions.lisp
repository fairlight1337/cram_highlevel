;;;
;;; Copyright (c) 2010, Lorenz Moesenlechner <moesenle@in.tum.de>
;;; All rights reserved.
;;; 
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions are met:
;;; 
;;;     * Redistributions of source code must retain the above copyright
;;;       notice, this list of conditions and the following disclaimer.
;;;     * Redistributions in binary form must reproduce the above copyright
;;;       notice, this list of conditions and the following disclaimer in the
;;;       documentation and/or other materials provided with the distribution.
;;;     * Neither the name of Willow Garage, Inc. nor the names of its
;;;       contributors may be used to endorse or promote products derived from
;;;       this software without specific prior written permission.
;;; 
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
;;; LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;;; CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;;; POSSIBILITY OF SUCH DAMAGE.
;;;

(in-package :designators-ros)

(defparameter *fixed-frame* "map")
(defparameter *robot-base-frame* "base_footprint")
(defparameter *distance-equality-threshold* 0.025)
(defparameter *angle-equality-threshold* (* 5 (/ pi 180)))

;;; We need to place these methods here because in the designator
;;; package, we don't have a notion of poses, just more or less
;;; abstract interfaces

(defmethod designator-pose ((desig location-designator))
  (reference desig))

(defmethod designator-distance ((desig-1 location-designator) (desig-2 location-designator))
  (cl-transforms:v-dist
   (cl-transforms:origin (reference desig-1))
   (cl-transforms:origin (reference desig-2))))

(defgeneric ensure-pose-stamped (position-object frame-id stamp)
  (:method ((pose cl-transforms:pose) frame-id stamp)
    (tf:pose->pose-stamped frame-id stamp pose))
  (:method ((pose-stamped tf:pose-stamped) frame-id stamp)
    (declare (ignore frame-id stamp))
    pose-stamped))

(defmethod designator-solutions-equal
    ((solution-1 cl-transforms:pose) (solution-2 cl-transforms:pose))
  "Checks whether two designator solutions are equal in *fixed-frame* or *robot-base-frame*."
  ;; two predicates used to implement equality check
  (labels ((transform-available-p (source-frame target-frame &key (time 0.0) (timeout 2.0))
             ;; Auxiliary predicate to check whether a tf-transform is available."
             (cl-tf2:has-transform *tf2* target-frame source-frame time timeout))
           (poses-equal-in-frame-p (pose-1 pose-2 compare-frame)
             ;; Predicate to check equality of two poses w.r.t. a given frame."
             (when (and (transform-available-p
                         compare-frame (tf:frame-id pose-1)
                         :time (tf:stamp pose-1))
                        (transform-available-p
                         compare-frame (tf:frame-id pose-2)
                         :time (tf:stamp pose-2)))
               ;; assert: both poses can be transformed into 'compare-frame'
               (let ((pose-1-transformed
                       (cl-tf2:do-transform *tf2* pose-1 compare-frame))
                     (pose-2-transformed
                       (cl-tf2:do-transform *tf2* pose-2 compare-frame)))
                 ;; compare transformed poses using pre-defined thresholds
                 (and (< (cl-transforms:v-dist
                      (cl-transforms:origin pose-1-transformed)
                      (cl-transforms:origin pose-2-transformed))
                     *distance-equality-threshold*)
                  (< (cl-transforms:angle-between-quaternions
                      (cl-transforms:orientation pose-1-transformed)
                      (cl-transforms:orientation pose-2-transformed))
                     *angle-equality-threshold*))))))
    ;; actual check: first making sure to have pose-stamped
    (let ((pose-1 (ensure-pose-stamped solution-1 *fixed-frame* 0.0))
          (pose-2 (ensure-pose-stamped solution-2 *fixed-frame* 0.0)))
      ;; equality in either of the defined frames is sufficient for us
      (or (poses-equal-in-frame-p pose-1 pose-2 *fixed-frame*)
          (poses-equal-in-frame-p pose-1 pose-2 *robot-base-frame*)))))

(defmethod reference :around ((designator location-designator) &optional role)
  (declare (ignore role))
  (ensure-pose-stamped (call-next-method) *fixed-frame* 0.0))
