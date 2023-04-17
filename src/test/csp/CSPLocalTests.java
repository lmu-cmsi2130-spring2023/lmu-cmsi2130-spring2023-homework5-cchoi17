package test.csp;

import static org.junit.Assert.*;

import org.junit.AfterClass;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.jupiter.api.*;
import org.junit.rules.TestWatcher;
import org.junit.rules.Timeout;
import org.junit.runner.Description;

import java.time.LocalDate;
import java.util.*;
import main.csp.*;
import static main.csp.CSPLocalSolver.*;

public class CSPLocalTests {
    
    // =================================================
    // Test Configuration
    // =================================================
    
    // Global timeout to prevent infinite loops from
    // crashing the test suite + to test that your
    // constraint propagation is working...
    @Rule
    public Timeout globalTimeout = Timeout.seconds(2);
    
    // Grade record-keeping
    // Number of times each test is repeated to account for local search's
    // non-completeness guarantee
    static final int REPETITIONS = 10;
    // Number of repetitions that must be passed per test to get credit
    // (this is a very generous threshold, most will pass all repetitions).
    static final int THRESHOLD = 8;
    static Map<String, Integer> passedMap = new HashMap<>();
    
    private static void logSuccess (String name) {
        passedMap.put(name, passedMap.getOrDefault(name, 0) + 1);
    }
    
    // Used for grading, reports the total number of tests
    // passed over the total possible
    @AfterAll
    public static void gradeReport () {
        int passed = 0, possible = 0;
        System.out.println("============================");
        System.out.println("Tests Complete");
        for (Integer val : passedMap.values()) {
            if (val > THRESHOLD) { passed++; }
            possible++;
        }
        System.out.println(passed + " / " + possible + " passed!");
        if ((1.0 * passed / possible) >= 0.9) {
            System.out.println("[!] Nice job!"); // Automated acclaim!
        }
        System.out.println("============================");
    }
    
    /**
     * Tests whether a given solution to a CSP satisfies all constraints or not
     * @param soln Full instantiation of variables to assigned values, indexed by variable
     * @param constraints The set of constraints the solution must satisfy
     */
    public static void testSolution (List<LocalDate> soln, Set<DateConstraint> constraints) {
        if (soln == null) {
            fail("[X] You returned null (signalling no solution) where a solution was expected");
        }
        for (DateConstraint d : constraints) {
            LocalDate leftDate = soln.get(d.L_VAL),
                      rightDate = (d.arity() == 1) 
                          ? ((UnaryDateConstraint) d).R_VAL 
                          : soln.get(((BinaryDateConstraint) d).R_VAL);
            
            if (!d.isSatisfiedBy(leftDate, rightDate)) {
                fail("[X] Constraint Failed: " + d);
            }
        }
    }
    
    /**
     * Helper method for generating uniform domains for tests.
     * @param n Number of meeting variables in this CSP.
     * @param startRange Start date for the range of each variable's domain.
     * @param endRange End date for the range of each variable's domain.
     * @return The List of Meeting-indexed MeetingDomains.
     */
    public static List<MeetingDomain> generateDomains (int n, LocalDate startRange, LocalDate endRange) {
        List<MeetingDomain> domains = new ArrayList<>();
        while (n > 0) {
            domains.add(new MeetingDomain(startRange, endRange));
            n--;
        }
        return domains;
    }
    
    
    // =================================================
    // Unit Tests
    // =================================================
    
    // CSPSolver Tests
    // -------------------------------------------------
    @RepeatedTest(value=REPETITIONS, name="t0")
    public void solve_t0(TestInfo testInfo) {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "==", LocalDate.of(2023, 1, 3))
            )
        );
        
        List<LocalDate> solution = solve(
            1,                          // Number of meetings to schedule
            LocalDate.of(2023, 1, 1),   // Domain start date
            LocalDate.of(2023, 1, 5),   // Domain end date
            constraints                 // Constraints all meetings must satisfy
        );
        
        testSolution(solution, constraints);
        logSuccess(testInfo.getDisplayName());
    }
    
    @RepeatedTest(value=REPETITIONS, name="t1")
    public void solve_t1(TestInfo testInfo) {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "==", LocalDate.of(2023, 1, 6))
            )
        );
        
        List<LocalDate> solution = solve(
            1,
            LocalDate.of(2023, 1, 1),
            LocalDate.of(2023, 1, 5),
            constraints
        );
        
        assertNull(solution);
        logSuccess(testInfo.getDisplayName());
    }
    
    @RepeatedTest(value=REPETITIONS, name="t2")
    public void solve_t2(TestInfo testInfo) {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "!=", 1),
                new BinaryDateConstraint(1, "==", 2),
                new BinaryDateConstraint(2, "!=", 3),
                new BinaryDateConstraint(3, "==", 4),
                new BinaryDateConstraint(4, "<", 0),
                new BinaryDateConstraint(3, ">", 2)
            )
        );
        
        List<LocalDate> solution = solve(
            5,
            LocalDate.of(2023, 1, 1),
            LocalDate.of(2023, 1, 3),
            constraints
        );
        
        testSolution(solution, constraints);
        logSuccess(testInfo.getDisplayName());
    }
    
    @RepeatedTest(value=REPETITIONS, name="t3")
    public void solve_t3(TestInfo testInfo) {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, ">", LocalDate.of(2023, 1, 1)),
                new UnaryDateConstraint(1, ">", LocalDate.of(2023, 2, 1)),
                new UnaryDateConstraint(2, ">", LocalDate.of(2023, 3, 1)),
                new UnaryDateConstraint(3, ">", LocalDate.of(2023, 4, 1)),
                new UnaryDateConstraint(4, ">", LocalDate.of(2023, 5, 1)),
                new BinaryDateConstraint(0, ">", 4),
                new BinaryDateConstraint(1, ">", 3),
                new BinaryDateConstraint(2, "!=", 3),
                new BinaryDateConstraint(4, "!=", 0),
                new BinaryDateConstraint(3, ">", 2)
            )
        );
        
        List<LocalDate> solution = solve(
            5,
            LocalDate.of(2023, 1, 1),
            LocalDate.of(2023, 5, 15),
            constraints
        );
        
        testSolution(solution, constraints);
        logSuccess(testInfo.getDisplayName());
    }
    
    // [!] This is the first test that (for-realsies) will show improvements of your local
    // search strategy over traditional backtracking -- the others were warmups!
    @RepeatedTest(value=REPETITIONS, name="t4")
    public void solve_t4(TestInfo testInfo) {
        final int N_CONS = 50;
        Set<DateConstraint> constraints = new HashSet<>();
        
        for (int i = 1; i < N_CONS/2; i++) {
            for (int j = N_CONS/2; j < N_CONS; j++) {
                if (i == j) { continue; }
                constraints.add(new BinaryDateConstraint(i, (i % 2 == 0) ? ">" : "<", j));
            }
        }
        
        List<LocalDate> solution = solve(
            N_CONS,
            LocalDate.of(2023, 1, 1),
            LocalDate.of(2023, 5, 30),
            constraints
        );
        
        testSolution(solution, constraints);
        logSuccess(testInfo.getDisplayName());
    }
    
}
