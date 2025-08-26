# Forest Friends Frenzy - ACL2 Logic Puzzle Implementation

This repository contains a formal implementation of the Forest Friends Frenzy logic puzzle using ACL2 (A Computational Logic for Applicative Common Lisp) for theorem proving and solution verification.

## Game Description

Forest Friends Frenzy is a logic puzzle set in the Hundred Acre Wood featuring four beloved characters:

- **Friends**: Winnie the Pooh, Piglet, Tigger, and Eeyore
- **Activities**: Honey tasting, bouncing, exploring, and gardening  
- **Time Slots**: Morning, noon, afternoon, and evening

### Puzzle Constraints

1. Tigger does his favorite activity earlier in the day than Eeyore
2. The friend who loves honey tasting performs their activity later than the friend who enjoys exploring
3. Piglet performs his favorite activity in the morning
4. Winnie the Pooh does not like gardening

### Solution

| Friend | Activity | Time of Day |
|--------|----------|-------------|
| Winnie the Pooh | Honey Tasting | Afternoon |
| Piglet | Bouncing | Morning |
| Tigger | Exploring | Noon |
| Eeyore | Gardening | Evening |

## Files

- `forest-friends-frenzy.lisp` - Complete ACL2 implementation with formal verification
- `forest-friends-frenzy-demo.ipynb` - Interactive Jupyter notebook demonstrating the solution
- `README.md` - This documentation file

## ACL2 Implementation Features

### Formal Verification
- **Data Structures**: Precise definitions for friends, activities, and time slots
- **Constraint Functions**: Each puzzle rule encoded as a verifiable ACL2 function
- **Solution Validation**: Automated checking of solution completeness and correctness
- **Theorem Proving**: Formal proofs that the canonical solution is valid

### Key Functions

```lisp
;; Check if a solution satisfies all constraints
(valid-solution-p solution)

;; Individual constraint checkers
(constraint1-p solution)  ; Tigger before Eeyore
(constraint2-p solution)  ; Honey tasting after exploring  
(constraint3-p solution)  ; Piglet in morning
(constraint4-p solution)  ; Pooh not gardening

;; Interactive verification
(verify-user-solution solution)
(show-canonical-solution)
```

## Usage

### With ACL2

1. Start ACL2:
   ```bash
   acl2
   ```

2. Load the implementation:
   ```lisp
   (ld "forest-friends-frenzy.lisp")
   ```

3. Verify the canonical solution:
   ```lisp
   (verify-user-solution *canonical-solution*)
   ```

4. Test your own solution:
   ```lisp
   (verify-user-solution '((pooh . (honey-tasting . afternoon))
                          (piglet . (bouncing . morning))
                          (tigger . (exploring . noon))
                          (eeyore . (gardening . evening))))
   ```

### With Jupyter Notebook

1. Open the demo notebook:
   ```bash
   jupyter notebook forest-friends-frenzy-demo.ipynb
   ```

2. Run the cells to see:
   - Problem domain definition
   - Constraint encoding and verification
   - Solution generation and uniqueness proof
   - Interactive testing of valid and invalid solutions

## Mathematical Properties

The ACL2 implementation formally proves:

1. **Completeness**: The canonical solution assigns exactly one activity and time to each friend
2. **Correctness**: The solution satisfies all four constraints
3. **Uniqueness**: There is exactly one valid solution to the puzzle
4. **Consistency**: The constraints are logically consistent and non-contradictory

## Educational Value

This implementation demonstrates:

- **Formal Methods**: Using theorem proving for puzzle verification
- **Constraint Satisfaction**: Encoding logic puzzles as formal constraints
- **Proof Techniques**: Mechanized reasoning about problem solutions
- **Software Verification**: Ensuring correctness through mathematical proof

## Development

### Requirements
- ACL2 theorem prover
- Common Lisp implementation (SBCL, CCL, etc.)
- Jupyter notebook (for interactive demo)

### Testing
The implementation includes comprehensive tests for:
- Individual constraint validation
- Solution completeness checking  
- Invalid solution detection
- Edge case handling

### Extensions
The framework can be extended to:
- Add new constraints
- Modify puzzle parameters
- Create similar logic puzzles
- Generate random puzzle instances

## License

This project is licensed under the MIT License - see the LICENSE.md file for details.

## Contributing

Contributions are welcome! Please feel free to submit pull requests for:
- Additional test cases
- Performance improvements
- Documentation enhancements
- New puzzle variations

## References

- [ACL2 Home Page](http://www.cs.utexas.edu/users/moore/acl2/)
- [ACL2 Documentation](http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/)
- [Logic Puzzles and Formal Methods](https://en.wikipedia.org/wiki/Constraint_satisfaction_problem)
