#!/usr/bin/env python3
"""
Simple test script to verify the Forest Friends Frenzy implementation works correctly.
This script tests the Python implementation that mirrors the ACL2 version.
"""

def time_order(time):
    order = {'morning': 1, 'noon': 2, 'afternoon': 3, 'evening': 4}
    return order.get(time, 0)

def earlier_time_p(time1, time2):
    return time_order(time1) < time_order(time2)

def check_constraint1(solution):
    """Tigger does his favorite activity earlier than Eeyore"""
    tigger_time = solution.get('tigger', {}).get('time')
    eeyore_time = solution.get('eeyore', {}).get('time')
    return tigger_time and eeyore_time and earlier_time_p(tigger_time, eeyore_time)

def check_constraint2(solution):
    """Honey tasting happens later than exploring"""
    honey_friend = None
    exploring_friend = None
    
    for friend, data in solution.items():
        if data.get('activity') == 'honey-tasting':
            honey_friend = friend
        elif data.get('activity') == 'exploring':
            exploring_friend = friend
    
    if honey_friend and exploring_friend:
        honey_time = solution[honey_friend]['time']
        exploring_time = solution[exploring_friend]['time']
        return earlier_time_p(exploring_time, honey_time)
    return False

def check_constraint3(solution):
    """Piglet performs his activity in the morning"""
    return solution.get('piglet', {}).get('time') == 'morning'

def check_constraint4(solution):
    """Pooh does not like gardening"""
    return solution.get('pooh', {}).get('activity') != 'gardening'

def verify_solution(solution):
    """Verify if a solution satisfies all constraints"""
    constraints = [
        ("Constraint 1 (Tigger before Eeyore)", check_constraint1),
        ("Constraint 2 (Honey tasting after exploring)", check_constraint2),
        ("Constraint 3 (Piglet in morning)", check_constraint3),
        ("Constraint 4 (Pooh not gardening)", check_constraint4)
    ]
    
    results = {}
    all_passed = True
    
    for name, check_func in constraints:
        passed = check_func(solution)
        results[name] = passed
        all_passed = all_passed and passed
    
    return all_passed, results

def print_solution_table(solution, title="Solution"):
    print(f"\n{title}:")
    print("=" * 50)
    print(f"{'Friend':<15} {'Activity':<15} {'Time of Day':<12}")
    print("-" * 50)
    
    for friend in ['pooh', 'piglet', 'tigger', 'eeyore']:
        if friend in solution:
            activity = solution[friend].get('activity', '').replace('-', ' ').title()
            time = solution[friend].get('time', '').title()
            friend_name = friend.replace('pooh', 'Winnie the Pooh').title()
            print(f"{friend_name:<15} {activity:<15} {time:<12}")
        else:
            print(f"{friend.title():<15} {'???':<15} {'???':<12}")

def main():
    print("Forest Friends Frenzy - ACL2 Logic Puzzle Test")
    print("=" * 60)
    
    # The canonical solution
    canonical_solution = {
        'pooh': {'activity': 'honey-tasting', 'time': 'afternoon'},
        'piglet': {'activity': 'bouncing', 'time': 'morning'},
        'tigger': {'activity': 'exploring', 'time': 'noon'},
        'eeyore': {'activity': 'gardening', 'time': 'evening'}
    }
    
    print_solution_table(canonical_solution, "Canonical Solution")
    
    valid, results = verify_solution(canonical_solution)
    
    print("\nConstraint Verification:")
    print("=" * 40)
    for constraint, passed in results.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{constraint}: {status}")
    
    print("=" * 40)
    print(f"Overall result: {'✓ VALID SOLUTION' if valid else '✗ INVALID SOLUTION'}")
    
    # Test an invalid solution
    print("\n" + "=" * 60)
    invalid_solution = {
        'pooh': {'activity': 'gardening', 'time': 'afternoon'},  # Violates constraint 4
        'piglet': {'activity': 'bouncing', 'time': 'morning'},
        'tigger': {'activity': 'exploring', 'time': 'noon'},
        'eeyore': {'activity': 'honey-tasting', 'time': 'evening'}
    }
    
    print_solution_table(invalid_solution, "Invalid Solution (for testing)")
    
    valid, results = verify_solution(invalid_solution)
    
    print("\nConstraint Verification:")
    print("=" * 40)
    for constraint, passed in results.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{constraint}: {status}")
    
    print("=" * 40)
    print(f"Overall result: {'✓ VALID SOLUTION' if valid else '✗ INVALID SOLUTION'}")
    
    print("\n" + "=" * 60)
    print("Test completed successfully!")
    print("The ACL2 implementation provides formal verification of these results.")

if __name__ == "__main__":
    main()
