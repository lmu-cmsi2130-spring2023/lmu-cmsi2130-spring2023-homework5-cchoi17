package main.csp;

import java.time.LocalDate;
import java.util.*;

/**
 * CSP: Calendar Satisfaction Problem Solver
 * Provides a solution for scheduling some n meetings in a given
 * period of time and according to some unary and binary constraints
 * on the dates of each meeting.
 */
public class CSPSolver {

    // Backtracking CSP Solver
    // --------------------------------------------------------------------------------------------------------------

    /**
     * Public interface for the CSP solver in which the number of meetings,
     * range of allowable dates for each meeting, and constraints on meeting
     * times are specified.
     * 
     * @param nMeetings   The number of meetings that must be scheduled, indexed
     *                    from 0 to n-1
     * @param rangeStart  The start date (inclusive) of the domains of each of the n
     *                    meeting-variables
     * @param rangeEnd    The end date (inclusive) of the domains of each of the n
     *                    meeting-variables
     * @param constraints Date constraints on the meeting times (unary and binary
     *                    for this assignment)
     * @return A list of dates that satisfies each of the constraints for each of
     *         the n meetings,
     *         indexed by the variable they satisfy, or null if no solution exists.
     */
    public static List<LocalDate> solve(int nMeetings, LocalDate rangeStart, LocalDate rangeEnd,
            Set<DateConstraint> constraints) {

        List<MeetingDomain> varDomains = new ArrayList<>();
        List<LocalDate> assignment = new ArrayList<>();
        for (int i = 0; i < nMeetings; i++) {
            varDomains.add(i, new MeetingDomain(rangeStart, rangeEnd));
        }
        nodeConsistency(varDomains, constraints);
        arcConsistency(varDomains, constraints);
        recursiveBacktracking(assignment, constraints, varDomains);
        if (assignment.isEmpty()) {
            System.out.println("empty");
            return null;
        }
        return assignment;
    }

    private static List<LocalDate> recursiveBacktracking(List<LocalDate> assignment,
            Set<DateConstraint> constraints, List<MeetingDomain> varDomains) {

        if (varDomains.size() == assignment.size()) {
            return assignment;
        }
        int index = assignment.size();
        for (MeetingDomain p : varDomains) {
            for (LocalDate i : p.domainValues) {
                assignment.add(index, i);
                boolean allSatisfied = true;
                for (DateConstraint thisConstraint : constraints) {
                    if (thisConstraint.L_VAL >= assignment.size()) {
                        continue;
                    }
                    if (thisConstraint.arity() == 2
                            && ((BinaryDateConstraint) thisConstraint).R_VAL >= assignment.size()) {
                        continue;
                    }
                    LocalDate leftDate = assignment.get(thisConstraint.L_VAL);
                    LocalDate rightDate = (thisConstraint.arity() == 1)
                            ? ((UnaryDateConstraint) thisConstraint).R_VAL
                            : assignment.get(((BinaryDateConstraint) thisConstraint).R_VAL);

                    if (!thisConstraint.isSatisfiedBy(leftDate, rightDate)) {
                        allSatisfied = false;
                    }
                }
                if (allSatisfied) {
                    List<LocalDate> result = recursiveBacktracking(assignment, constraints, varDomains);
                    if (result != null) {
                        return result;
                    }
                }
                assignment.remove(index);
            }
        }
        return null;
    }
    //
    // Filtering Operations
    // --------------------------------------------------------------------------------------------------------------

    /**
     * Enforces node consistency for all variables' domains given in varDomains
     * based on
     * the given constraints. Meetings' domains correspond to their index in the
     * varDomains List.
     * 
     * @param varDomains  List of MeetingDomains in which index i corresponds to D_i
     * @param constraints Set of DateConstraints specifying how the domains should
     *                    be constrained.
     *                    [!] Note, these may be either unary or binary constraints,
     *                    but this method should only process
     *                    the *unary* constraints!
     */
    public static void nodeConsistency(List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {
        for (DateConstraint j : constraints) {
            if (j.arity() == 2) {
                continue;
            }
            MeetingDomain tailDomain = varDomains.get(j.L_VAL);
            Set<LocalDate> tailDomVals = new HashSet<>();
            tailDomVals.addAll(tailDomain.domainValues);
            for (LocalDate k : tailDomain.domainValues) {
                if (!j.isSatisfiedBy(k, ((UnaryDateConstraint) j).R_VAL)) {
                    tailDomVals.remove(k);
                }
            }
            tailDomain.domainValues = tailDomVals;
        }
    }

    /**
     * Enforces arc consistency for all variables' domains given in varDomains based
     * on
     * the given constraints. Meetings' domains correspond to their index in the
     * varDomains List.
     * 
     * @param varDomains  List of MeetingDomains in which index i corresponds to D_i
     * @param constraints Set of DateConstraints specifying how the domains should
     *                    be constrained.
     *                    [!] Note, these may be either unary or binary constraints,
     *                    but this method should only process
     *                    the *binary* constraints using the AC-3 algorithm!
     */
    public static void arcConsistency(List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {
        Set<Arc> queue = new HashSet<>();
        for (DateConstraint j : constraints) {
            if (j.arity() == 1) {
                continue;
            }
            queue.add(new Arc(j.L_VAL, ((BinaryDateConstraint) j).R_VAL, j));
            queue.add(new Arc(((BinaryDateConstraint) j).R_VAL, j.L_VAL,
                    ((BinaryDateConstraint) j).getReverse()));
        }
        Set<Arc> fullQueue = new HashSet<>();
        fullQueue.addAll(queue);
        while (!queue.isEmpty()) {
            Arc first = queue.iterator().next();
            queue.remove(first);
            if (removeInconsistentVal(first, varDomains)) {
                for (Arc i : fullQueue) {
                    if (i.HEAD == first.TAIL) {
                        queue.add(i);
                    }
                }
            }
        }
    }

    private static boolean removeInconsistentVal(Arc first, List<MeetingDomain> varDomains) {
        boolean removed = false;
        MeetingDomain tailDomain = varDomains.get(first.TAIL);
        MeetingDomain headDomain = varDomains.get(first.HEAD);
        Set<LocalDate> tailDomVals = new HashSet<>();
        tailDomVals.addAll(tailDomain.domainValues);
        for (LocalDate i : tailDomain.domainValues) {
            boolean consistent = false;
            for (LocalDate j : headDomain.domainValues) {
                if (first.CONSTRAINT.isSatisfiedBy(i, j)) {
                    consistent = true;
                }
            }
            if (consistent == false) {
                tailDomVals.remove(i);
                removed = true;
            }
        }
        tailDomain.domainValues = tailDomVals;
        return removed;
    }

    /**
     * Private helper class organizing Arcs as defined by the AC-3 algorithm, useful
     * for implementing the
     * arcConsistency method.
     * [!] You may modify this class however you'd like, its basis is just a
     * suggestion that will indeed work.
     */
    private static class Arc {

        public final DateConstraint CONSTRAINT;
        public final int TAIL, HEAD;

        /**
         * Constructs a new Arc (tail -> head) where head and tail are the meeting
         * indexes
         * corresponding with Meeting variables and their associated domains.
         * 
         * @param tail Meeting index of the tail
         * @param head Meeting index of the head
         * @param c    Constraint represented by this Arc.
         *             [!] WARNING: A DateConstraint's isSatisfiedBy method is
         *             parameterized as:
         *             isSatisfiedBy (LocalDate leftDate, LocalDate rightDate), meaning
         *             L_VAL for the first
         *             parameter and R_VAL for the second. Be careful with this when
         *             creating Arcs that reverse
         *             direction. You may find the BinaryDateConstraint's getReverse
         *             method useful here.
         */
        public Arc(int tail, int head, DateConstraint c) {
            this.TAIL = tail;
            this.HEAD = head;
            this.CONSTRAINT = c;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (this.getClass() != other.getClass()) {
                return false;
            }
            Arc otherArc = (Arc) other;
            return this.TAIL == otherArc.TAIL && this.HEAD == otherArc.HEAD
                    && this.CONSTRAINT.equals(otherArc.CONSTRAINT);
        }

        @Override
        public int hashCode() {
            return Objects.hash(this.TAIL, this.HEAD, this.CONSTRAINT);
        }

        @Override
        public String toString() {
            return "(" + this.TAIL + " -> " + this.HEAD + ")";
        }

    }

}
