using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Google.OrTools.Sat;


public class ShiftSchedulingSat
{
    static void Main()
    {
        Stopwatch stopwatch = new Stopwatch();
        stopwatch.Start();


        // data 
        int numEmployees = 60;
        int femaleEmployees = (numEmployees /10) *7;
        int numDays = 7;
        int numShifts = 3;
        string[] workfields = { "Cashier", "Rayon", "Store" };
        string[] shiftNames = { "Morning", "Afternoon", "Night" };
        Random random = new Random();

        // employees for the each day 
        var employeesPerShift = new int[numDays, numShifts];
        for (int d = 0; d < numDays; d++)
        {
            for (int s = 0; s < numShifts; s++)
            {
                employeesPerShift[d, s] = random.Next(40, 60); 
            }
        }

        var genders = new bool[numEmployees];
        for (int i = 0; i < femaleEmployees; i++)
        {
            genders[i] = false;  // female
        }
        for (int i = femaleEmployees; i < numEmployees; i++)
        {
            genders[i] = true;   // male
        }
        // randomizes gender distribution
        for (int i = genders.Length - 1; i > 0; i--)
        {
            int j = random.Next(i + 1);
            bool temp = genders[i];
            genders[i] = genders[j];
            genders[j] = temp;
        }

        // model
        CpModel model = new CpModel();

        // shift var
        var shifts = new Dictionary<(int, int, int), IntVar>();
        foreach (var e in Range(numEmployees))
        {
            foreach (var d in Range(numDays))
            {
                foreach (var s in Range(numShifts))
                {
                    shifts[(e, d, s)] = model.NewBoolVar($"shift_e{e}_d{d}_s{s}");
                }
            }
        }

        // workfields
        var workfieldVars = new Dictionary<(int, int, int, int), IntVar>(); // IntVar is a variable type that can hold integer and boolean variables same time 
        foreach (var e in Range(numEmployees))
        {
            foreach (var d in Range(numDays))
            {
                foreach (var s in Range(numShifts))
                {
                    foreach (var w in Range(workfields.Length))
                    {
                        workfieldVars[(e, d, s, w)] = model.NewBoolVar($"workfield_e{e}_d{d}_s{s}_w{w}");
                    }
                }
            }
        }

        // ensure dynamic number of employees per shift
        foreach (var d in Range(numDays))
        {
            foreach (var s in Range(numShifts))
            {
                var literals = new List<ILiteral>();
                foreach (var e in Range(numEmployees))
                {
                    literals.Add((ILiteral)shifts[(e, d, s)]);
                }
                model.Add(LinearExpr.Sum(literals.ToArray()) == employeesPerShift[d, s]); // constraints number of employees that works every shift
            } // but It can't check which employees work that day only checks the number of employees assigned 
        }

        // specific workfield distribution for each shift (modified to percentage for dynamic employee count)
        var workfieldDistribution = new Dictionary<int, (double, double, double)>
        {
            {0, (0.15, 0.25, 0.60)},
            {1, (0.10, 0.65, 0.25)},
            {2, (0.15, 0.60, 0.25)}
        };

        foreach (var d in Range(numDays))
        {
            foreach (var s in Range(numShifts))
            {
                var (cashierMargin, rayonMargin, storeMargin) = workfieldDistribution[s];
                int numEmployeesShift = employeesPerShift[d, s];

                int numCashiers = (int)(numEmployeesShift * cashierMargin);
                int numRayon = (int)(numEmployeesShift * rayonMargin);
                int numStore = (int)(numEmployeesShift * storeMargin);

                foreach (var w in Range(workfields.Length))
                {
                    var workfieldLiterals = new List<ILiteral>();
                    foreach (var e in Range(numEmployees))
                    {
                        model.Add(workfieldVars[(e, d, s, w)] <= shifts[(e, d, s)]); // if an employee doesnt work on that shift it can't have a workfield on that shift too
                        workfieldLiterals.Add((ILiteral)workfieldVars[(e, d, s, w)]); // sums the boolean variables of every employees on every shift 
                    }
                    if (w == 0) model.Add(LinearExpr.Sum(workfieldLiterals.ToArray()) == numCashiers); // cashiers count must be equal to number of cashiers constraint
                    if (w == 1) model.Add(LinearExpr.Sum(workfieldLiterals.ToArray()) == numRayon); // rayons count must be equal to number of rayons constraint
                    if (w == 2) model.Add(LinearExpr.Sum(workfieldLiterals.ToArray()) == numStore); // stores count must be equal to number of stores constraint
                }
            }
        }

        // each employee works in only one workfield per shift
        foreach (var e in Range(numEmployees))
        {
            foreach (var d in Range(numDays))
            {
                foreach (var s in Range(numShifts))
                {
                    var workfieldLiterals = new List<ILiteral>(); // adds every shifts data to the list as boolean variables 
                    foreach (var w in Range(workfields.Length)) // iterates every workfield 
                    {
                        workfieldLiterals.Add((ILiteral)workfieldVars[(e, d, s, w)]); 
                    }
                    model.Add(LinearExpr.Sum(workfieldLiterals.ToArray()) <= 1); // LinearExpr.Sum sums every boolean variable and <= adds constraint that there can not be  2 assigment for an employee that shift 
                }
            }
        }

        // gender constraints for afternoon and night shifts
        foreach (var d in Range(numDays))
        {
            foreach (var s in new[] { 1, 2 }) // afternoon and night shifts only
            {
                var rayonFemalesLiterals = new List<ILiteral>();
                var cashierFemalesLiterals = new List<ILiteral>();
                var rayonTotalLiterals = new List<ILiteral>();
                var cashierTotalLiterals = new List<ILiteral>();

                foreach (var e in Range(numEmployees))
                {
                    if (!genders[e])
                    {
                        rayonFemalesLiterals.Add((ILiteral)workfieldVars[(e, d, s, 1)]); // rayon
                        cashierFemalesLiterals.Add((ILiteral)workfieldVars[(e, d, s, 0)]); // cashier
                    }
                    rayonTotalLiterals.Add((ILiteral)workfieldVars[(e, d, s, 1)]); // rayon
                    cashierTotalLiterals.Add((ILiteral)workfieldVars[(e, d, s, 0)]); // cashier
                }

                // 40 percent on rayon
                model.Add(LinearExpr.Sum(rayonFemalesLiterals.ToArray()) * 10 >= LinearExpr.Sum(rayonTotalLiterals.ToArray()) * 4);

                // 80 percent in cashier
                model.Add(LinearExpr.Sum(cashierFemalesLiterals.ToArray()) * 10 >= LinearExpr.Sum(cashierTotalLiterals.ToArray()) * 8);
            }
        }

        // dummy objective in case there is no solution
        model.Minimize(LinearExpr.Constant(0)); // Doesn't do anything used because there is no objective function  
        //we only want to check if constraints are working 

        // solver
        CpSolver solver = new CpSolver();
        var status = solver.Solve(model);

        // random assignment
        var workfieldAssignments = new Dictionary<(int, int, int), string>();
        foreach (var e in Range(numEmployees))
        {
            foreach (var d in Range(numDays))
            {
                foreach (var s in Range(numShifts))
                {
                    workfieldAssignments[(e, d, s)] = workfields[random.Next(workfields.Length)];
                }
            }
        }

        // print (optimized in case of runtime)
        if (status == CpSolverStatus.Optimal || status == CpSolverStatus.Feasible)
        {
            Console.WriteLine("Solution:");

            // store assignments
            var assignments = new Dictionary<(int day, int shift), List<(int employee, string workfield, string gender)>>();

            foreach (var d in Range(numDays))
            {
                foreach (var s in Range(numShifts))
                {
                    var shiftAssignments = new List<(int employee, string workfield, string gender)>();

                    foreach (var e in Range(numEmployees))
                    {
                        if (solver.BooleanValue((ILiteral)shifts[(e, d, s)]))
                        {
                            for (var w = 0; w < workfields.Length; w++)
                            {
                                if (solver.BooleanValue((ILiteral)workfieldVars[(e, d, s, w)]))
                                {
                                    shiftAssignments.Add((e, workfields[w], genders[e] ? "Male" : "Female"));
                                    break;
                                }
                            }
                        }
                    }
                    assignments[(d, s)] = shiftAssignments;
                }
            }

            // print stored assignments
            foreach (var d in Range(numDays))
            {
                Console.WriteLine($"Day {d + 1}:");
                foreach (var s in Range(numShifts))
                {
                    Console.WriteLine($"  {shiftNames[s]} Shift:");
                    foreach (var (employee, workfield, gender) in assignments[(d, s)])
                    {
                        Console.WriteLine($"    Employee {employee} ({gender}) - Workfield: {workfield}");
                    }
                    // print the number of employees for the shift
                    Console.WriteLine($"    Number of Employees: {assignments[(d, s)].Count}");
                }
            }
        }
        else
        {
            Console.WriteLine("No solution found.");
        }
        // Stop the stopwatch and print the elapsed time
        stopwatch.Stop();
        Console.WriteLine($"Execution Time: {stopwatch.ElapsedMilliseconds} ms");
    }
    
    static IEnumerable<int> Range(int start, int stop)
    {
        foreach (var i in Enumerable.Range(start, stop - start))
            yield return i;
    }

    static IEnumerable<int> Range(int stop)
    {
        return Range(0, stop);
    }
}
