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

(in-package :cram-task-knowledge)


(defgeneric examine-perceived-object-designator
    (original-designator object-designator))
(defgeneric location-valid (template object))
(defgeneric designators-match (template subject))
(defgeneric filter-perceived-objects (template-designator perceived-objects))
(defgeneric filter-objects (template-designator perceived-objects))

(define-hook objects-perceived (object-template object-designators))


(defmethod examine-perceived-object-designator
    ((original-designator desig:object-designator)
     (object-designator desig:object-designator))
  "Enriches a perceived object designator `object-designator' with
additional information from the reasoning system. First, the type is
infered (if not set already either manually in the requesting
designator, or the one returned from the perception system), and then
additional properties are infered and appended to the designator's
description."
  (let* ((object-description (desig:description
                              object-designator))
         (type (or (desig:desig-prop-value object-designator
                                           'desig-props:type)
                   (cut:with-vars-bound (?type)
                       (first
                        (crs:prolog `(infer-object-property
                                      ,object-designator
                                      desig-props:type ?type)))
                     (unless (eql ?type '?type)
                       ?type))
                   (desig:desig-prop-value original-designator
                                           'desig-props:type)))
         (typed-object-designator
           (or (and (or (eql type '?type) (not type)) object-designator)
               (desig:make-designator
                'object
                (append
                 (remove-if (lambda (x) (eql (car x) 'type))
                            object-description)
                 `((type ,type)))
                object-designator)))
         (new-properties
           (cut:force-ll (cut:lazy-mapcar
                          (lambda (bdgs)
                            (cut:with-vars-bound (?key ?value) bdgs
                              `(,?key ,?value)))
                          (crs:prolog `(infer-object-property
                                        ,typed-object-designator
                                        ?key ?value)))))
         (refined-old
           (remove-if (lambda (x)
                        (find x new-properties
                              :test (lambda (x y)
                                      (eql (car x) (car y)))))
                      (desig:description
                       typed-object-designator))))
    (let* ((infered-description (append refined-old new-properties))
           (complete-description
             (let ((original-description
                     (desig:description original-designator)))
               (append infered-description
                       (cpl:mapcar-clean
                        (lambda (original-property)
                          (unless (find original-property
                                        infered-description
                                        :test (lambda (x y)
                                                (eql (car x) (car y))))))
                        original-description)))))
      (desig:make-designator
       'object complete-description object-designator))))

(defgeneric filter-perceived-objects (object-template perceived-objects)
  (:documentation "Filters all perceived objects according to all registered filters. This method is mainly used by perception process modules that want to validate and filter their results. Also, this function triggers the `object-perceived-event' plan event, updating the belief state.")
  (:method (object-template perceived-objects)
    (let* ((filtered-objects
             (loop for filter-result in (objects-perceived object-template perceived-objects)
                   append filter-result)))
      (dolist (object filtered-objects)
        (cram-plan-knowledge:on-event
         (make-instance
          'cram-plan-knowledge:object-perceived-event
          :perception-source :robosherlock-pm
          :object-designator object)))
      filtered-objects)))

(defmethod location-valid ((template object-designator)
                           (object object-designator))
  (let ((at-template (desig-prop-value template 'desig-props::at))
        (at-object (desig-prop-value object 'desig-props::at)))
    (cond (at-template
           (let ((first-at (first-desig at-template)))
             (cond ((desig-prop-value at-object 'desig-props::pose) t)
                   (t (validate-location-designator-solution
                       first-at
                       (slot-value at-object
                                   'desig::current-solution))))))
          (t t))))

(defmethod designators-match ((template object-designator)
                              (subject object-designator))
  "Checks every property of the `template' object designator to be
present in the `subject' object designator. Returns `t' if all
properties in `template' are satisfied, `NIL' otherwise. Only checks
for: string, number, symbol. All other value types are ignored. This
way, reference and unknown object type comparisons are avoided."
  (cond ((let ((type-1 (desig-prop-value template 'desig-props::type))
               (type-2 (desig-prop-value subject 'desig-props::type)))
           (and (not (eql type-1 nil))
                (eql type-1 type-2))))
        (t
         (cond ((eql (desig-prop-value subject 'type)
                     'desig-props::semantic-handle)
                (and (eql (desig-prop-value template 'type)
                          'desig-props::semantic-handle)
                     (string= (desig-prop-value template 'name)
                              (desig-prop-value subject 'name))))
               (t
                (loop for (key value) in (description template)
                      for type-check-fnc = (cond ((stringp value)
                                                  #'string=)
                                                 ((numberp value)
                                                  #'=)
                                                 ((symbolp value)
                                                  #'eql))
                      for subject-values = (desig-prop-values
                                            subject key)
                      when (and type-check-fnc subject-values)
                        do (unless (find value subject-values
                                         :test type-check-fnc)
                             (return nil))
                      finally (return t))
                ;t
                ))))) ;; NOTE(winkler): This is a hack.

(defmethod filter-objects ((template-designator object-designator)
                           (perceived-objects list))
  "Filters out all object designator instances in the
`perceived-objects' list which descriptions don't match the properties
defined in `template-designator' or whose location doesn't fit into
the original location designator's described area, if applicable."
  (cpl:mapcar-clean
   (lambda (perceived-object)
     (when (and (designators-match template-designator perceived-object)
                (location-valid template-designator perceived-object))
       ;; The designator matches based on its description (if
       ;; any). Now see if it gets accepted based on external factors.
       perceived-object))
   perceived-objects))
