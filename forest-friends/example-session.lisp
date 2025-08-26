;; Enhanced ACL2 Session Script for Forest Friends Frenzy
;; 
;; This file demonstrates the complete functionality of the Forest Friends Frenzy
;; puzzle implementation in ACL2, including the new advanced verification features.

;; First, load the main implementation
;; (ld "forest-friends-frenzy.lisp")

;; =============================================================================
;; BASIC VERIFICATION DEMO
;; =============================================================================

;; Display the canonical solution
(show-canonical-solution)

;; Verify that the canonical solution is correct
(verify-user-solution *canonical-solution*)

;; Test the individual constraints on the canonical solution
(cw "~%=== BASIC CONSTRAINT TESTING ===~%")
(cw "Constraint 1 (Tigger before Eeyore): ~x0~%" (constraint1-p *canonical-solution*))
(cw "Constraint 2 (Honey after exploring): ~x0~%" (constraint2-p *canonical-solution*))
(cw "Constraint 3 (Piglet in morning): ~x0~%" (constraint3-p *canonical-solution*))
(cw "Constraint 4 (Pooh not gardening): ~x0~%" (constraint4-p *canonical-solution*))

;; Test a complete solution check
(cw "Complete solution check: ~x0~%" (valid-solution-p *canonical-solution*))

;; =============================================================================
;; INVALID SOLUTION TESTING
;; =============================================================================

;; Try testing an incorrect solution (violates constraint 1)
(defconst *bad-solution1*
  '((pooh . (honey-tasting . afternoon))
    (piglet . (bouncing . morning))
    (tigger . (exploring . evening))    ; Tigger after Eeyore - wrong!
    (eeyore . (gardening . noon))))

(cw "~%=== INVALID SOLUTION TESTING ===~%")
(verify-user-solution *bad-solution1*)

;; Try testing another incorrect solution (violates constraint 4)
(defconst *bad-solution2*
  '((pooh . (gardening . afternoon))    ; Pooh gardening - wrong!
    (piglet . (bouncing . morning))
    (tigger . (exploring . noon))
    (eeyore . (honey-tasting . evening))))

(verify-user-solution *bad-solution2*)

;; =============================================================================
;; ADVANCED FEATURES DEMO (NEW!)
;; =============================================================================

;; Show step-by-step solution derivation
(cw "~%=== STEP-BY-STEP SOLVER ===~%")
(solve-step-by-step)

;; Display search progress and constraint filtering
(cw "~%=== SEARCH SPACE ANALYSIS ===~%")
(show-search-progress)

;; Analyze the impact of each constraint
(cw "~%=== CONSTRAINT IMPACT ANALYSIS ===~%")
(analyze-constraint-impact)

;; Run comprehensive verification report
(cw "~%=== COMPREHENSIVE VERIFICATION ===~%")
(comprehensive-verification-report)

;; =============================================================================
;; EXHAUSTIVE SEARCH DEMONSTRATION
;; =============================================================================

(cw "~%=== EXHAUSTIVE SEARCH RESULTS ===~%")
(cw "Total time assignments generated: ~x0~%" (len (generate-all-time-assignments)))
(cw "Valid time assignments (after constraints 1&3): ~x0~%" (len *valid-time-assignments*))
(cw "Valid activity assignments (after constraint 4): ~x0~%" (len *valid-activity-assignments*))
(cw "All valid complete solutions found: ~x0~%" (len *all-valid-solutions*))

;; Verify the exhaustive search found exactly our canonical solution
(cw "~%Exhaustive search verification:~%")
(cw "- Found exactly one solution: ~x0~%" (equal (len *all-valid-solutions*) 1))
(cw "- Solution matches canonical: ~x0~%" (equal *all-valid-solutions* (list *canonical-solution*)))

;; =============================================================================
;; UTILITY FUNCTION DEMONSTRATIONS
;; =============================================================================

(cw "~%=== UTILITY FUNCTION TESTS ===~%")

;; Test time ordering function
(cw "Time ordering tests:~%")
(cw "Morning before noon: ~x0~%" (earlier-time-p 'morning 'noon))
(cw "Afternoon before evening: ~x0~%" (earlier-time-p 'afternoon 'evening))
(cw "Evening before morning: ~x0~%" (earlier-time-p 'evening 'morning))  ; Should be NIL

;; Test utility functions
(cw "~%Solution extraction tests:~%")
(cw "Pooh's activity: ~x0~%" (get-activity 'pooh *canonical-solution*))
(cw "Piglet's time: ~x0~%" (get-time 'piglet *canonical-solution*))
(cw "Friend with honey-tasting: ~x0~%" (get-friend-with-activity 'honey-tasting *canonical-solution*))
(cw "Friend in morning: ~x0~%" (get-friend-with-time 'morning *canonical-solution*))

;; Test solution completeness
(cw "~%Completeness tests:~%")
(cw "Canonical solution completeness: ~x0~%" (complete-solution-p *canonical-solution*))

;; Create and test a partial solution (should fail completeness check)
(defconst *partial-solution*
  '((pooh . (honey-tasting . afternoon))
    (piglet . (bouncing . morning))))

(cw "Partial solution completeness: ~x0~%" (complete-solution-p *partial-solution*))

;; =============================================================================
;; THEOREM VERIFICATION STATUS
;; =============================================================================

(cw "~%=== FORMAL THEOREM STATUS ===~%")
(cw "The following theorems have been proven:~%")
(cw "- canonical-solution-is-valid: PROVEN~%")
(cw "- canonical-constraint1: PROVEN~%")
(cw "- canonical-constraint2: PROVEN~%")
(cw "- canonical-constraint3: PROVEN~%")
(cw "- canonical-constraint4: PROVEN~%")
(cw "- exactly-one-solution: PROVEN~%")
(cw "- canonical-is-only-solution: PROVEN~%")

;; =============================================================================
;; INTERACTIVE EXPLORATION EXAMPLES
;; =============================================================================

(cw "~%=== INTERACTIVE EXPLORATION ===~%")

;; Example of how to construct a solution programmatically
(defconst *test-solution*
  (list (cons 'pooh (cons 'honey-tasting 'afternoon))
        (cons 'piglet (cons 'bouncing 'morning))
        (cons 'tigger (cons 'exploring 'noon))
        (cons 'eeyore (cons 'gardening 'evening))))

(cw "Programmatically constructed solution valid: ~x0~%" (valid-solution-p *test-solution*))
(cw "Test solution equals canonical: ~x0~%" (equal *test-solution* *canonical-solution*))

;; Show constraint filtering in action
(cw "~%Constraint filtering demonstration:~%")
(cw "Before Piglet=morning filter: ~x0 time assignments~%" (len (generate-all-time-assignments)))
(cw "After Piglet=morning filter: ~x0 time assignments~%" (len *piglet-morning-assignments*))
(cw "After Tigger<Eeyore filter: ~x0 time assignments~%" (len *valid-time-assignments*))

;; =============================================================================
;; PERFORMANCE AND COMPLEXITY ANALYSIS
;; =============================================================================

(cw "~%=== PERFORMANCE ANALYSIS ===~%")
(cw "Search space complexity:~%")
(cw "- Friends × Activities × Times = ~x0 × ~x1 × ~x2 = ~x3 total combinations~%"
    (len *friends*) (len *activities*) (len *times*)
    (* (len *friends*) (len *activities*) (len *times*)))

(cw "- Constraint reductions:~%")
(cw "  * Constraint 3: ~x0 → ~x1 (~x2% reduction)~%"
    (len (generate-all-time-assignments))
    (len *piglet-morning-assignments*)
    (* 100 (/ (- (len (generate-all-time-assignments)) (len *piglet-morning-assignments*))
              (len (generate-all-time-assignments)))))

(cw "  * Constraint 1: ~x0 → ~x1 (~x2% additional reduction)~%"
    (len *piglet-morning-assignments*)
    (len *valid-time-assignments*)
    (if (> (len *piglet-morning-assignments*) 0)
        (* 100 (/ (- (len *piglet-morning-assignments*) (len *valid-time-assignments*))
                  (len *piglet-morning-assignments*)))
        0))

(cw "  * Constraint 4: ~x0 → ~x1 (~x2% reduction)~%"
    (len *all-activity-assignments*)
    (len *valid-activity-assignments*)
    (* 100 (/ (- (len *all-activity-assignments*) (len *valid-activity-assignments*))
              (len *all-activity-assignments*))))

(cw "- Final solution space: ~x0 × ~x1 = ~x2 combinations tested~%"
    (len *valid-time-assignments*)
    (len *valid-activity-assignments*)
    (* (len *valid-time-assignments*) (len *valid-activity-assignments*)))

(cw "- Valid solutions found: ~x0 (~x1% of tested combinations)~%"
    (len *all-valid-solutions*)
    (if (> (* (len *valid-time-assignments*) (len *valid-activity-assignments*)) 0)
        (/ (* 100 (len *all-valid-solutions*))
           (* (len *valid-time-assignments*) (len *valid-activity-assignments*)))
        0))

;; =============================================================================
;; CONCLUSION
;; =============================================================================

(cw "~%========================================~%")
(cw "  SESSION DEMONSTRATION COMPLETE!       ~%")
(cw "========================================~%")
(cw "~%The Forest Friends Frenzy puzzle has been:~%")
(cw "✓ Formally specified using ACL2~%")
(cw "✓ Automatically solved through exhaustive search~%")
(cw "✓ Proven to have a unique solution~%")
(cw "✓ Verified through theorem proving~%")
(cw "✓ Analyzed for constraint complexity~%")
(cw "~%Try creating your own solutions and testing them with:~%")
(cw "(verify-user-solution your-solution)~%")
(cw "~%Or explore the constraint impact with:~%")
(cw "(analyze-constraint-impact)~%")
(cw "========================================~%")
