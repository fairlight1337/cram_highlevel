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
;;;     * Neither the name of Universitaet Bremen nor the names of its
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

(in-package :cram-task-knowledge)

(def-fact-group inference-facts (infer-object-property object-handle)
  
  (<- (object-handle ?type ?handle)
    (crs:fail))
  
  (<- (infer-object-property ?object ?key ?value)
    (crs:fail)))

(def-fact-group object-validity-facts (perceived-object-invalid)
  
  (<- (perceived-object-invalid ?object)
    (crs:fail)))

(def-fact-group perception-request-enrichment (volume-of-interest)
  
  (<- (obj-volume-of-interest ?obj ?p ?w ?h ?d)
    (current-designator ?obj ?current-obj)
    (desig-prop ?current-obj (at ?loc))
    (current-designator ?loc ?current-loc)
    (loc-volume-of-interest ?current-loc ?p ?w ?h ?d))

  (<- (obj-volume-of-interest ?obj nil nil nil)
    (crs:true))
  
  (<- (loc-volume-of-interest ?loc ?p ?w ?h ?d)
    (desig-prop ?loc (on ?on))
    (semantic-map-costmap::semantic-map-desig-objects ?loc ?objects)
    (member ?obj ?objects)
    (semantic-map-object->volume-of-interest ?obj ?p ?w ?h ?d))

  (<- (loc-volume-of-interest ?loc nil nil nil nil)
    (crs:true))
  
  (<- (semantic-map-object->volume-of-interest ?obj ?p ?w ?h ?d)
    (crs:lisp-fun semantic-map-object->volume-of-interest
                  ?obj :on ?result)
    (not (equal ?result nil))
    (equal ?result (?p ?w ?h ?d))))

(defun semantic-map-object->volume-of-interest (semantic-map-object
                                                &optional (relation :on))
  (let ((pose (sem-map-utils::pose semantic-map-object))
        (dimensions (sem-map-utils::dimensions semantic-map-object)))
    (case relation
      (:on (let ((above-surface-threshold 0.3)
                 (origin (tf:origin pose)))
             `(,(tf:make-pose-stamped
                 "/map" 0.0
                 (tf:make-3d-vector (tf:x origin) (tf:y origin)
                                    (+ (tf:z origin)
                                       (/ above-surface-threshold 2)))
                 (tf:orientation pose))
               ,(/ (tf:x dimensions) 2)
               ,(/ (tf:y dimensions) 2)
               ,(/ above-surface-threshold 2)))))))

(defun refine-description (description)
  (let* ((object-designator (make-designator 'object description))
         (new-properties
          (cut:force-ll (cut:lazy-mapcar
                         (lambda (bdgs)
                           (cut:with-vars-bound (?key ?value) bdgs
                             `(,?key ,?value)))
                         (crs:prolog `(infer-object-property
                                       ,object-designator
                                       ?key ?value))))))
    (let ((refined-old
            (remove-if (lambda (x)
                         (find x new-properties
                               :test (lambda (x y)
                                       (eql (car x) (car y)))))
                       description)))
      (append refined-old new-properties))))
