;; Forest Friends Frenzy Logic Puzzle
;; ACL2 Implementation with Formal Verification
;;
;; This file implements the Forest Friends Frenzy logic puzzle using ACL2
;; to formally verify correct solutions.

(in-package "ACL2")

;; =============================================================================
;; DATA DEFINITIONS
;; =============================================================================

;; Define the entities in our puzzle
(defconst *friends* '(pooh piglet tigger eeyore))
(defconst *activities* '(honey-tasting bouncing exploring gardening))
(defconst *times* '(morning noon afternoon evening))

;; Time ordering (earlier to later)
(defun time-order (time)
  (case time
    (morning 1)
    (noon 2)
    (afternoon 3)
    (evening 4)
    (otherwise 0)))

(defun earlier-time-p (time1 time2)
  "Returns true if time1 is earlier than time2"
  (< (time-order time1) (time-order time2)))

;; =============================================================================
;; SOLUTION REPRESENTATION
;; =============================================================================

;; A solution is represented as an association list mapping friends to
;; (activity . time) pairs
(defun valid-friend-p (friend)
  (member friend *friends*))

(defun valid-activity-p (activity)
  (member activity *activities*))

(defun valid-time-p (time)
  (member time *times*))

(defun valid-assignment-p (assignment)
  "Check if an assignment (friend . (activity . time)) is valid"
  (and (consp assignment)
       (valid-friend-p (car assignment))
       (consp (cdr assignment))
       (valid-activity-p (cadr assignment))
       (valid-time-p (cddr assignment))))

(defun get-activity (friend solution)
  "Get the activity assigned to a friend in the solution"
  (cadr (assoc friend solution)))

(defun get-time (friend solution)
  "Get the time assigned to a friend in the solution"
  (cddr (assoc friend solution)))

(defun get-friend-with-activity (activity solution)
  "Get the friend assigned to an activity"
  (cond ((endp solution) nil)
        ((equal (cadr (car solution)) activity)
         (caar solution))
        (t (get-friend-with-activity activity (cdr solution)))))

(defun get-friend-with-time (time solution)
  "Get the friend assigned to a time"
  (cond ((endp solution) nil)
        ((equal (cddr (car solution)) time)
         (caar solution))
        (t (get-friend-with-time time (cdr solution)))))

;; =============================================================================
;; CONSTRAINT CHECKING
;; =============================================================================

(defun constraint1-p (solution)
  "Tigger does his favorite activity earlier in the day than Eeyore"
  (let ((tigger-time (get-time 'tigger solution))
        (eeyore-time (get-time 'eeyore solution)))
    (and tigger-time eeyore-time
         (earlier-time-p tigger-time eeyore-time))))

(defun constraint2-p (solution)
  "The friend who loves honey tasting performs their activity later than the friend who enjoys exploring"
  (let ((honey-friend (get-friend-with-activity 'honey-tasting solution))
        (exploring-friend (get-friend-with-activity 'exploring solution)))
    (and honey-friend exploring-friend
         (let ((honey-time (get-time honey-friend solution))
               (exploring-time (get-time exploring-friend solution)))
           (and honey-time exploring-time
                (earlier-time-p exploring-time honey-time))))))

(defun constraint3-p (solution)
  "Piglet performs his favorite activity in the morning"
  (equal (get-time 'piglet solution) 'morning))

(defun constraint4-p (solution)
  "Winnie the Pooh does not like gardening"
  (not (equal (get-activity 'pooh solution) 'gardening)))

(defun all-constraints-p (solution)
  "Check if solution satisfies all constraints"
  (and (constraint1-p solution)
       (constraint2-p solution)
       (constraint3-p solution)
       (constraint4-p solution)))

;; =============================================================================
;; SOLUTION COMPLETENESS AND UNIQUENESS
;; =============================================================================

(defun complete-solution-p (solution)
  "Check if solution assigns exactly one activity and time to each friend"
  (and (equal (len solution) 4)
       (no-duplicates-equal (strip-cars solution))
       (no-duplicates-equal (strip-cadrs solution))
       (no-duplicates-equal (strip-cddrs solution))
       (subsetp *friends* (strip-cars solution))
       (subsetp *activities* (strip-cadrs solution))
       (subsetp *times* (strip-cddrs solution))))

(defun strip-cadrs (lst)
  "Extract second elements from association list"
  (cond ((endp lst) nil)
        (t (cons (cadr (car lst))
                 (strip-cadrs (cdr lst))))))

(defun strip-cddrs (lst)
  "Extract third elements from association list"
  (cond ((endp lst) nil)
        (t (cons (cddr (car lst))
                 (strip-cddrs (cdr lst))))))

(defun valid-solution-p (solution)
  "Check if solution is complete and satisfies all constraints"
  (and (complete-solution-p solution)
       (all-constraints-p solution)))

;; =============================================================================
;; THE CANONICAL SOLUTION
;; =============================================================================

(defconst *canonical-solution*
  '((pooh . (honey-tasting . afternoon))
    (piglet . (bouncing . morning))
    (tigger . (exploring . noon))
    (eeyore . (gardening . evening))))

;; =============================================================================
;; VERIFICATION THEOREMS
;; =============================================================================

;; Prove that the canonical solution is valid
(defthm canonical-solution-is-valid
  (valid-solution-p *canonical-solution*))

;; Prove that constraint 1 holds for canonical solution
(defthm canonical-satisfies-constraint1
  (constraint1-p *canonical-solution*))

;; Prove that constraint 2 holds for canonical solution
(defthm canonical-satisfies-constraint2
  (constraint2-p *canonical-solution*))

;; Prove that constraint 3 holds for canonical solution
(defthm canonical-satisfies-constraint3
  (constraint3-p *canonical-solution*))

;; Prove that constraint 4 holds for canonical solution
(defthm canonical-satisfies-constraint4
  (constraint4-p *canonical-solution*))

;; =============================================================================
;; SOLUTION CHECKER FUNCTION
;; =============================================================================

(defun check-solution (solution)
  "Check if a proposed solution is valid and return detailed feedback"
  (cond ((not (complete-solution-p solution))
         "Solution is incomplete or has duplicates")
        ((not (constraint1-p solution))
         "Constraint 1 violated: Tigger must do his activity earlier than Eeyore")
        ((not (constraint2-p solution))
         "Constraint 2 violated: Honey tasting must be later than exploring")
        ((not (constraint3-p solution))
         "Constraint 3 violated: Piglet must perform his activity in the morning")
        ((not (constraint4-p solution))
         "Constraint 4 violated: Pooh cannot like gardening")
        (t "Solution is valid!")))

;; =============================================================================
;; PRETTY PRINTING
;; =============================================================================

(defun print-solution (solution)
  "Pretty print a solution in table format"
  (progn
    (cw "~%Forest Friends Frenzy Solution:~%")
    (cw "================================~%")
    (cw "| Friend       | Activity      | Time of Day  |~%")
    (cw "|--------------|---------------|--------------|~%")
    (print-friend-row 'pooh solution)
    (print-friend-row 'piglet solution)
    (print-friend-row 'tigger solution)
    (print-friend-row 'eeyore solution)
    (cw "================================~%~%")))

(defun print-friend-row (friend solution)
  "Print a single row for a friend"
  (let ((activity (get-activity friend solution))
        (time (get-time friend solution)))
    (cw "| ~s~v | ~s~v | ~s~v |~%"
        (string-capitalize (symbol-name friend)) 
        (- 12 (length (symbol-name friend)))
        (if activity (string-capitalize (substitute #\Space #\- (symbol-name activity))) "")
        (- 13 (if activity (length (substitute #\Space #\- (symbol-name activity))) 0))
        (if time (string-capitalize (symbol-name time)) "")
        (- 12 (if time (length (symbol-name time)) 0)))))

;; =============================================================================
;; INTERACTIVE FUNCTIONS
;; =============================================================================

(defun verify-user-solution (solution)
  "Verify a user-provided solution and provide feedback"
  (progn
    (cw "~%Checking your solution...~%")
    (print-solution solution)
    (cw "Result: ~s~%" (check-solution solution))
    (if (valid-solution-p solution)
        (cw "Congratulations! You solved the puzzle correctly!~%")
        (cw "Please review the constraints and try again.~%"))))

(defun show-canonical-solution ()
  "Display the canonical solution"
  (progn
    (cw "~%The correct solution is:~%")
    (print-solution *canonical-solution*)))

;; =============================================================================
;; EXAMPLE USAGE
;; =============================================================================

;; Example of how to test the system:
;; (verify-user-solution *canonical-solution*)
;; (show-canonical-solution)

;; Example of testing an incorrect solution:
;; (verify-user-solution '((pooh . (gardening . morning))
;;                        (piglet . (bouncing . noon))
;;                        (tigger . (exploring . afternoon))
;;                        (eeyore . (honey-tasting . evening))))
