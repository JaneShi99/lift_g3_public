/*
Step 3 demo: the Sylow-subgroup eliminator (sylowEliminator,
src/pgroup/sylowEliminator.m) on the 15 instances of the paper's dataset
where Steps 1 and 2 leave more than one candidate triple.  Input is the list
of Step-2 candidates [a1, a2, a3]; PASS means the eliminator returns the
group order of the true candidate.
*/
SetColumns(0);
AttachSpec("./src/g3/g3Hybrid.spec");
AttachSpec("./src/pgroup/sylowEliminator.spec");
load "./src/general/lpolyBoundHelper.m";
SetSeed(2025);

MAX_RANK := 6;  // Jac(C)(F_p) has rank at most 2g = 6

R<x,y,z> := PolynomialRing(Integers(), 3);

// <p, quartic, Step-2 candidate [a1, a2, a3] triples, index of the true candidate>
instances := [*
    < 1861, x^2*y^2 + x^3*z - y^3*z + x*y*z^2 + 2*x*z^3 - 2*y*z^3,
      [ [114,9915,479180], [114,4332,267026], [114,8054,408462], [114,6193,337744] ], 1 >,
    < 1861, x^2*y^2 + x*y^3 + x^3*z + y^3*z - 3*x*y*z^2 - 2*x*z^3 - 2*y*z^3 - z^4,
      [ [-126,7153,-386736], [-126,9014,-464898], [-126,10875,-543060], [-126,5292,-308574] ], 3 >,
    < 1607, x^2*y^2 + y^4 + x^3*z + 2*x*y^2*z + y^2*z^2 + x*z^3,
      [ [0,3214,0], [0,0,0], [0,4821,0], [0,1607,0], [0,-1607,0] ], 3 >,
    < 1663, x^2*y^2 + y^4 + x^3*z + 2*x*y^2*z + y^2*z^2 + x*z^3,
      [ [0,4989,0], [0,1663,0], [0,-1663,0], [0,3326,0], [0,0,0] ], 1 >,
    < 1697, x^4 + 3*x^2*y^2 + 2*y^4 + 2*x^3*z + 3*x^2*y*z + 3*x*y^2*z + 4*y^3*z + 4*x^2*z^2 + 3*x*y*z^2 + 7*y^2*z^2 + 3*x*z^3 + 5*y*z^3 + 3*z^4,
      [ [126,6989,359184], [126,8686,430458], [126,10383,501732] ], 3 >,
    < 1601, x^3*y + x^2*y^2 + x*y^3 + x^3*z + x^2*y*z + x*y^2*z + y^3*z + x^2*z^2 + y^2*z^2 - 2*x*z^3 - 2*y*z^3 + z^4,
      [ [42,-1013,47572], [42,2189,92400], [42,5391,137228], [42,588,69986], [42,3790,114814] ], 3 >,
    < 1601, -y^4 + x^3*z + x*y^2*z - 2*y^3*z + x^2*z^2 + x*y*z^2 - 2*y^2*z^2 + x*z^3 - y*z^3,
      [ [-6,12,-9614], [-6,-1589,-6412], [-6,3214,-16018], [-6,1613,-12816], [-6,4815,-19220] ], 5 >,
    < 1627, -y^4 + x^3*z + x*y^2*z - 2*y^3*z + x^2*z^2 + x*y*z^2 - 2*y^2*z^2 + x*z^3 - y*z^3,
      [ [84,5606,249732], [84,725,113064], [84,3979,204176], [84,-902,67508], [84,7233,295288], [84,2352,158620] ], 5 >,
    < 1753, -y^4 + x^3*z + x*y^2*z - 2*y^3*z + x^2*z^2 + x*y*z^2 - 2*y^2*z^2 + x*z^3 - y*z^3,
      [ [-78,275,-108732], [-78,5534,-245466], [-78,2028,-154310], [-78,7287,-291044], [-78,-1478,-63154], [-78,3781,-199888] ], 4 >,
    < 1607, 2*x^2*y^2 - y^4 + x^3*z + 2*x^2*y*z - x*y^2*z - 2*y^3*z - x*y*z^2 - 3*y^2*z^2 - 2*x*z^3 - 2*y*z^3 - z^4,
      [ [90,2700,171630], [90,4307,219840], [90,5914,268050], [90,1093,123420], [90,7521,316260] ], 5 >,
    < 1667, 2*x^2*y^2 - y^4 + x^3*z + 2*x^2*y*z - x*y^2*z - 2*y^3*z - x*y*z^2 - 3*y^2*z^2 - 2*x*z^3 - 2*y*z^3 - z^4,
      [ [-36,-1235,-41736], [-36,432,-61740], [-36,2099,-81744], [-36,3766,-101748], [-36,5433,-121752] ], 5 >,
    < 1607, y^4 + x^3*z + 2*y^3*z + 4*x^2*z^2 + y^2*z^2 + x*z^3,
      [ [144,10126,496272], [144,11733,573408] ], 2 >,
    < 2027, x*y^3 + x^3*z + 3*x^2*y*z + 3*x*y^2*z + 3*x*y*z^2 + y*z^3,
      [ [132,11889,620312], [132,9862,531124], [132,7835,441936], [132,5808,352748] ], 1 >,
    < 1627, x^2*y^2 + x*y^3 - y^4 + 2*x^3*z + x^2*y*z - 2*x*y^2*z - y^3*z + 3*x^2*z^2 - 4*x*y*z^2 + 2*y^2*z^2 + 5*x*z^3 - 5*y*z^3,
      [ [84,5606,249732], [84,725,113064], [84,3979,204176], [84,-902,67508], [84,7233,295288], [84,2352,158620] ], 5 >,
    < 1601, y^4 + x^3*z - x*z^3,
      [ [-6,4815,-19220], [-6,12,-9614], [-6,3214,-16018], [-6,-1589,-6412], [-6,1613,-12816] ], 1 >
*];

runDemo := procedure()
    t0 := Cputime();
    verdicts := [];
    for n in [1..#instances] do
        p, f0, cands, truth := Explode(instances[n]);
        printf "=== instance %o: p = %o, %o candidates, truth = candidate %o ===\n", n, p, #cands, truth;
        orders := [ getJacSize(p, a[1], a[2], a[3]) : a in cands ];
        printf "candidate orders L_i(1) = %o\n", orders;

        t1 := Cputime();
        verdict := "ERROR";
        try
            J := G3JacHybridCreation(ChangeRing(f0, GF(p)));
            survivor := sylowEliminator(orders, J, MAX_RANK : verbose := true);
            idx := Index(orders, survivor);
            printf "  survivor: candidate %o, [a1,a2,a3] = %o\n", idx, cands[idx];
            verdict := idx eq truth select "PASS" else "WRONG CANDIDATE";
        catch e
            printf "  error: %o\n", e`Object;
        end try;
        printf "  %o  (%o s)\n\n", verdict, Cputime(t1);
        Append(~verdicts, verdict);
    end for;

    printf "=== summary ===\n";
    for n in [1..#instances] do
        printf "instance %o (p = %o): %o\n", n, instances[n][1], verdicts[n];
    end for;
    printf "%o / %o instances PASS; total CPU %o s\n",
        #[ v : v in verdicts | v eq "PASS" ], #instances, Cputime(t0);
end procedure;

runDemo();
