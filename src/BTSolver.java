import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

public class BTSolver
{

	// =================================================================
	// Properties
	// =================================================================

	private ConstraintNetwork network;
	private SudokuBoard sudokuGrid;
	private Trail trail;

	private boolean hasSolution = false;

	public String varHeuristics;
	public String valHeuristics;
	public String cChecks;

	// =================================================================
	// Constructors
	// =================================================================

	public BTSolver ( SudokuBoard sboard, Trail trail, String val_sh, String var_sh, String cc )
	{
		this.network    = new ConstraintNetwork( sboard );
		this.sudokuGrid = sboard;
		this.trail      = trail;

		varHeuristics = var_sh;
		valHeuristics = val_sh;
		cChecks       = cc;
	}

	// =================================================================
	// Consistency Checks
	// =================================================================

	// Basic consistency check, no propagation done
	private boolean assignmentsCheck ( )
	{
		for ( Constraint c : network.getConstraints() )
			if ( ! c.isConsistent() )
				return false;

		return true;
	}

	/**
	 * Forward Checking Heuristic
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * Return: true is assignment is consistent, false otherwise
	 */
	private boolean forwardChecking ( )
	{
		boolean doneFC = false;        // indicates if forward checking is done

	    while (!doneFC) {
	        doneFC = true;

	        // get all modified assigned variables
	        for (Constraint c : network.getModifiedConstraints()) {
	            for (Variable var : c.vars) {
	                if (var.isAssigned()) {

	                    // get neighbors of each variable
	                    for (Variable neighbor : network.getNeighborsOfVariable(var)) {

	                        // remove variable's assigned value from domain of neighbors
	                        if (neighbor.getDomain().contains(var.getAssignment())) {
	                            trail.push(neighbor);
	                            neighbor.removeValueFromDomain(var.getAssignment());

	                            // if any removal is done, forward checking continues
	                            doneFC = false;
	                        }
	                    }
	                }
	            }
	        }
	    }
	    // check if any domains are empty (board is not consistent)
	    for (Variable var : network.getVariables())
	        if (var.getDomain().isEmpty())
	            return false;
	    return true;
	}

	/**
	 * Norvig's Heuristics
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * (2) If a constraint has only one possible place for a value
	 *     then put the value there.
	 *
	 * Return: true is assignment is consistent, false otherwise
	 */
	private boolean norvigCheck ( )
	{
		bool doneFC = false;    // indicates if forward checking is done
	    while (!doneFC) {
	        doneFC = true;

	        // get all modified constraints
	        for (Constraint c : network.getModifiedConstraints()) {

	            // for every variable in constraint
	            for (Variable var : c.vars) {

	                // assigned variables need their values removed from the domains of their neighbors
	                if (var.isAssigned()) {
	                    for (Variable neighbor : network.getNeighborsOfVariable(var)) {

	                        // remove assigned value from domain of neighbor
	                        if (neighbor.getDomain().contains(var.getAssignment())) {
	                            trail.push(neighbor);
	                            neighbor.removeValueFromDomain(var.getAssignment());

	                            // if any removal is done, forward checking continues
	                            doneFC = false;
	                        }
	                    }
	                }
	                // unassigned variables need to be assigned if they can only be one value
	                else {
	                    // for every value in unassigned variable's domain
	                    for (int value : var.getDomain()) {

	                        // check if the value found in any neighbor's domain
	                        bool must_be_assigned = true;
	                        for (Variable neighbor : network.getNeighborsOfVariable(var)) {
	                            if (neighbor.getDomain().contains(value)) {
	                                must_be_assigned = false;
	                                break;
	                            }
	                        }

	                        // if value is not found in any neighbor's domain, assign to variable
	                        if (must_be_assigned) {
	                            trail.push(var);
	                            var.assignValue(value);

	                            doneFC = false;
	                            break;
	                        }
	                    }
	                }
	            }
	        }
	    }
	    // check if any domains are empty (board is not consistent)
	    for (Variable var : network.getVariables())
	        if (var.getDomain().isEmpty())
	            return false;
	    return true;
	}

	// =================================================================
	// Variable Selectors
	// =================================================================

	// Basic variable selector, returns first unassigned variable
	private Variable getfirstUnassignedVariable()
	{
		for ( Variable v : network.getVariables() )
			if ( ! v.isAssigned() )
				return v;

		// Everything is assigned
		return null;
	}

	/**
	 * Minimum Remaining Value Heuristic
	 *
	 * Return: The unassigned variable with the smallest domain
	 */
	private Variable getMRV ( )
	{
		Variable mrv = getfirstUnassignedVariable();
	    if (mrv != nullptr) {
	        int min_values = mrv.size();
	        for (Variable v : network.getVariables()) {
	            if (!(v.isAssigned()) && v.size() < min_values) {
	                mrv = v;
	                min_values = v.size();
	            }
	        }
	    }

	    return mrv;
	}

	/**
	 * Degree Heuristic
	 *
	 * Return: The unassigned variable with the most unassigned neighbors
	 */
	private Variable getDegree ( )
	{
		Variable mrv = getfirstUnassignedVariable();
	    if (mrv != null) {

	        // initialize list of mrvs to contain one mrv (first unassigned variable)
	        int min_values = mrv.size();
	        List<Variable> mrvs = new ArrayList<Variable>();
	        mrvs.add(mrv);

	        // store list of mrvs that all must have the smallest domain
	        for (Variable v : network.getVariables()) {
	            if (!(v.isAssigned())) {

	                // if an unassigned v has a smaller domain than the min
	                if (v.size() < min_values) {

	                    // reset min_values and restart list of mrvs
	                    mrvs.clear();
	                    mrvs.add(v);
	                    min_values = v.size();
	                }
	                    // variables with same number of values as min are added to list of mrvs
	                else if (v.size() == min_values)
	                    mrvs.add(v);
	            }
	        }

	        // tiebreaker: pick mrv with largest degree
	        mrv = mrvs.iterator().next();
	        int max_degree = 0;
	        for (Variable v : mrvs) {
	            int degree = 0;
	            for (Variable n : network.getNeighborsOfVariable(v))
	                if (!(n.isAssigned()))
	                    degree++;
	            if (degree > max_degree) {
	                mrv = v;
	                max_degree = degree;
	            }
	        }
	    }
	    return mrv;
	}

	/**
	 * Minimum Remaining Value Heuristic
	 * with Degree Heuristic as a Tie Breaker
	 *
	 * Return: The unassigned variable with, first, the smallest domain
	 *         and, second, the most unassigned neighbors
	 */
	private Variable MRVwithTieBreaker ( )
	{
		Variable mrv = getfirstUnassignedVariable();
	    if (mrv != nullptr) {

	        // initialize list of mrvs to contain one mrv (first unassigned variable)
	        int min_values = mrv.size();
	        List<Variable> mrvs = new ArrayList<Variable>();
	        mrvs.push_back(mrv);

	        // store list of mrvs that all must have the smallest domain
	        for (Variable v : network.getVariables()) {
	            if (!(v.isAssigned())) {

	                // if an unassigned v has a smaller domain than the min
	                if (v.size() < min_values) {

	                    // reset min_values and restart list of mrvs
	                    mrvs.clear();
	                    mrvs.push_back(v);
	                    min_values = v.size();
	                }
	                    // variables with same number of values as min are added to list of mrvs
	                else if (v.size() == min_values)
	                    mrvs.push_back(v);
	            }
	        }

	        // tiebreaker: pick mrv with largest number of constraints
	        mrv = mrvs.front();
	        int max_constraints = 0;
	        for (Variable v : mrvs) {
	            int constraints = 0;
	            for (Constraint c : network.getConstraintsContainingVariable(v))
	                for (Variable n : c.vars)
	                    if (!(n.isAssigned()))
	                        constraints++;
	            if (constraints > max_constraints) {
	                mrv = v;
	                max_constraints = constraints;
	            }
	        }
	    }
	    return mrv;
	}

	// =================================================================
	// Value Selectors
	// =================================================================

	// Default Value Ordering
	public List<Integer> getValuesInOrder ( Variable v )
	{
		List<Integer> values = v.getDomain().getValues();

		Comparator<Integer> valueComparator = new Comparator<Integer>(){

			@Override
			public int compare(Integer i1, Integer i2) {
				return i1.compareTo(i2);
			}
		};
		Collections.sort(values, valueComparator);
		return values;
	}

	/**
	 * Least Constraining Value Heuristic
	 *
	 * The Least constraining value is the one that will knock the least
	 * values out of it's neighbors domain.
	 *
	 * Return: A list of v's domain sorted by the LCV heuristic
	 *         The LCV is first and the MCV is last
	 */
	public List<Integer> getValuesLCVOrder ( Variable v )
	{
		List<Entry<Integer, Integer>> unsorted = new ArrayList<Entry<Integer, Integer>>();
	    List<Integer> return_vec = new ArrayList<Integer>();

	    for (int value : getValuesInOrder(v)) {
	        int count = 0;
	        for (Variable var : network.getNeighborsOfVariable(v))
	            if (var.getDomain().contains(value))
	                ++count;
	        unsorted.add(new Entry<Integer, Integer>(value, count));
	    }

	    for (Entry<Integer, Integer> i: unsorted)
	        return_vec.add(i.getKey());

	    return return_vec;
	}

	//==================================================================
	// Engine Functions
	//==================================================================

	public void solve ( )
	{
		if ( hasSolution )
			return;

		// Variable Selection
		Variable v = selectNextVariable();

		if ( v == null )
		{
			for ( Variable var : network.getVariables() )
			{
				// If all variables haven't been assigned
				if ( ! var.isAssigned() )
				{
					System.out.println( "Error" );
					return;
				}
			}

			// Success
			hasSolution = true;
			return;
		}

		// Attempt to assign a value
		for ( Integer i : getNextValues( v ) )
		{
			// Store place in trail and push variable's state on trail
			trail.placeTrailMarker();
			trail.push( v );

			// Assign the value
			v.assignValue( i );

			// Propagate constraints, check consistency, recurse
			if ( checkConsistency() )
				solve();

			// If this assignment succeeded, return
			if ( hasSolution )
				return;

			// Otherwise backtrack
			trail.undo();
		}
	}

	private boolean checkConsistency ( )
	{
		switch ( cChecks )
		{
			case "forwardChecking":
				return forwardChecking();

			case "norvigCheck":
				return norvigCheck();

			default:
				return assignmentsCheck();
		}
	}

	private Variable selectNextVariable ( )
	{
		switch ( varHeuristics )
		{
			case "MinimumRemainingValue":
				return getMRV();

			case "Degree":
				return getDegree();

			case "MRVwithTieBreaker":
				return MRVwithTieBreaker();

			default:
				return getfirstUnassignedVariable();
		}
	}

	public List<Integer> getNextValues ( Variable v )
	{
		switch ( valHeuristics )
		{
			case "LeastConstrainingValue":
				return getValuesLCVOrder( v );

			default:
				return getValuesInOrder( v );
		}
	}

	public boolean hasSolution ( )
	{
		return hasSolution;
	}

	public SudokuBoard getSolution ( )
	{
		return network.toSudokuBoard ( sudokuGrid.getP(), sudokuGrid.getQ() );
	}

	public ConstraintNetwork getNetwork ( )
	{
		return network;
	}
}
