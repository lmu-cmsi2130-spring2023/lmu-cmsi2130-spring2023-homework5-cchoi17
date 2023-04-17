package main.csp;

import java.time.LocalDate;
import java.util.*;

/**
 * UnaryDateConstraints are those in which one variable
 * is being compared by some operator, specified by an
 * int L_VAL (for the corresponding variable 
 * / meeting index) and LocalDate R_VAL, such as:
 * 0 == 2019-1-3
 *   OR
 * 3 <= 2019-11-9
 */
public class UnaryDateConstraint extends DateConstraint {

    public final LocalDate R_VAL;
    
    /**
     * Constructs a new UnaryDateConstraint of the format:
     *   lVal operator rVal
     * ...where:
     * @param lVal A meeting index
     * @param operator Operator comparing the mentioned lVal meeting to some date
     * @param rVal A date compared to the meeting in lVal
     */
    public UnaryDateConstraint (int lVal, String operator, LocalDate rVal) {
        super(lVal, operator, 1);
        this.R_VAL = rVal;
    }
    
    @Override
    public String toString () {
        return super.toString() + " " + this.R_VAL;
    }
    
    @Override
    public boolean equals (Object other) {
        if (this == other) { return true; }
        if (this.getClass() != other.getClass()) { return false; }
        UnaryDateConstraint otherDC = (UnaryDateConstraint) other;
        return (this.L_VAL == otherDC.L_VAL && this.OP.equals(otherDC.OP) && this.R_VAL.equals(otherDC.R_VAL));
    }
    
    @Override
    public int hashCode () {
        return Objects.hash(this.L_VAL) * Objects.hash(this.OP) * Objects.hash(this.R_VAL);
    }
    
    
}
