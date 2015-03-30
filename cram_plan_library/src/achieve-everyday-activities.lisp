;;; Copyright (c) 2015, Jan Winkler <winkler@cs.uni-bremen.de>
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
;;;     * Neither the name of University of Bremen nor the names of its
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

(in-package :plan-lib)

(def-goal (achieve (table-set ?table ?situation))
  (ros-info (achieve plan-lib) "(achieve (table-set))")
  (with-designators ((loc-on-table (location `((on Cupboard)
                                               (name ,?table))))
                     (generic-object (object `((at ,loc-on-table)))))
    (let ((necessary-objects (crs:prolog `(table-setting-object
                                           ,?situation ?object)))
          (objects-on-table (perceive-object 'all generic-object)))
      )))

(def-goal (perceive-object drawer-handle ?semantic-name)
  (let ((semantic-handle-reference
          (first (sem-map-utils:designator->semantic-map-objects
                  (make-designator
                   'object `((desig-props::name ,?semantic-name)))))))
    (when semantic-handle-reference
      (let* ((handle-name
               (concatenate 'string ?semantic-name "_handle"))
             (handle
               (first (perceive-object
                       'currently-visible
                       (make-designator
                        'object `((desig-props::type
                                   desig-props::semantic-handle)
                                  (desig-props::name ,handle-name))))))
             (handle-pose (desig-prop-value handle
                                            'desig-props:pose))
             (semantic-handle-pose
               (sem-map-utils:pose semantic-handle-reference))
             (handle-pose-map
               (tf:copy-pose-stamped
                (cl-tf2:do-transform
                 cram-roslisp-common::*tf2*
                 handle-pose "map")
                :orientation (tf:orientation
                              semantic-handle-pose))))
        (make-designator
         'object `((desig-props::name ,?semantic-name)
                   (desig-props::type desig-props::semantic-handle)
                   (desig-props::at
                    ,(make-designator
                      'location
                      `((desig-props::pose ,handle-pose-map))))))))))

(def-goal (achieve (drawer-opened ?semantic-name))
  (let ((semantic-handle (perceive-object
                          'drawer-handle ?semantic-name)))
    (unless semantic-handle
      (cpl:fail 'cram-plan-failures:object-not-found))
    (with-designators ((action-pull-open (action
                                          `((desig-props::type
                                             desig-props::trajectory)
                                            (desig-props:to
                                             desig-props::pull-open)
                                            (desig-props::handle
                                             ,semantic-handle)))))
      (perform action-pull-open))))
