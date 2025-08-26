;; Example ACL2 Session Script for Forest Friends Frenzy
;; 
;; This file demonstrates how to interact with the Forest Friends Frenzy
;; puzzle implementation in ACL2. Copy and paste these commands into
;; an ACL2 session after loading forest-friends-frenzy.lisp

;; First, load the main implementation
;; (ld "forest-friends-frenzy.lisp")

;; Display the canonical solution
(show-canonical-solution)

;; Verify that the canonical solution is correct
(verify-user-solution *canonical-solution*)

;; Test the individual constraints on the canonical solution
(constraint1-p *canonical-solution*)  ; Should return T
(constraint2-p *canonical-solution*)  ; Should return T  
(constraint3-p *canonical-solution*)  ; Should return T
(constraint4-p *canonical-solution*)  ; Should return T

;; Test a complete solution check
(valid-solution-p *canonical-solution*)  ; Should return T

;; Try testing an incorrect solution (violates constraint 1)
(defconst *bad-solution1*
  '((pooh . (honey-tasting . afternoon))
    (piglet . (bouncing . morning))
    (tigger . (exploring . evening))    ; Tigger after Eeyore - wrong!
    (eeyore . (gardening . noon))))

(verify-user-solution *bad-solution1*)

;; Try testing another incorrect solution (violates constraint 4)
(defconst *bad-solution2*
  '((pooh . (gardening . afternoon))    ; Pooh gardening - wrong!
    (piglet . (bouncing . morning))
    (tigger . (exploring . noon))
    (eeyore . (honey-tasting . evening))))

(verify-user-solution *bad-solution2*)

;; Test individual constraint functions
(cw "~%Testing individual constraints:~%")
(cw "Constraint 1 (Tigger before Eeyore): ~x0~%" (constraint1-p *canonical-solution*))
(cw "Constraint 2 (Honey after exploring): ~x0~%" (constraint2-p *canonical-solution*))
(cw "Constraint 3 (Piglet in morning): ~x0~%" (constraint3-p *canonical-solution*))
(cw "Constraint 4 (Pooh not gardening): ~x0~%" (constraint4-p *canonical-solution*))

;; Verify time ordering function
(cw "~%Time ordering tests:~%")
(cw "Morning before noon: ~x0~%" (earlier-time-p 'morning 'noon))
(cw "Afternoon before evening: ~x0~%" (earlier-time-p 'afternoon 'evening))
(cw "Evening before morning: ~x0~%" (earlier-time-p 'evening 'morning))  ; Should be NIL

;; Test utility functions
(cw "~%Utility function tests:~%")
(cw "Pooh's activity: ~x0~%" (get-activity 'pooh *canonical-solution*))
(cw "Piglet's time: ~x0~%" (get-time 'piglet *canonical-solution*))
(cw "Friend with honey-tasting: ~x0~%" (get-friend-with-activity 'honey-tasting *canonical-solution*))
(cw "Friend in morning: ~x0~%" (get-friend-with-time 'morning *canonical-solution*))

;; Test solution completeness
(cw "~%Solution completeness test: ~x0~%" (complete-solution-p *canonical-solution*))

;; Create and test a partial solution (should fail completeness check)
(defconst *partial-solution*
  '((pooh . (honey-tasting . afternoon))
    (piglet . (bouncing . morning))))

(cw "~%Partial solution completeness test: ~x0~%" (complete-solution-p *partial-solution*))

;; Example of how to construct a solution programmatically
(defconst *test-solution*
  (list (cons 'pooh (cons 'honey-tasting 'afternoon))
        (cons 'piglet (cons 'bouncing 'morning))
        (cons 'tigger (cons 'exploring 'noon))
        (cons 'eeyore (cons 'gardening 'evening))))

(cw "~%Programmatically constructed solution valid: ~x0~%" (valid-solution-p *test-solution*))

;; Show that our test solution equals the canonical solution
(cw "Test solution equals canonical: ~x0~%" (equal *test-solution* *canonical-solution*))

(cw "~%Session demonstration complete!~%")
(cw "Try creating your own solutions and testing them with verify-user-solution!~%")
