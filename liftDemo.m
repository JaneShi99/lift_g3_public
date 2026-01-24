load "./src/general/lpolyBSGS.m";

P2<x,y,z> := ProjectiveSpace(Rationals(), 2);

// Define unique curves
C1 := x^2*y^2 + 2*x*y^3 + y^4 + x^3*z + x^2*y*z + x*y^2*z + x^2*z^2 - 2*x*y*z^2 - 2*x*z^3 - y*z^3 - z^4;
C2 := x^2*y^2 + x*y^3 + x^3*z + x*y^2*z + y^3*z - x^2*z^2 - 3*x*y*z^2 + 2*y^2*z^2 + x*z^3;
C3 := x*y^3 + x^3*z + 2*x*y^2*z + y^3*z - y*z^3 - z^4;
C4 := x^2*y^2 + x^3*z + x^2*y*z - x*y^2*z + y^3*z + 2*y^2*z^2 + x*z^3 - z^4;
C5 := x^3*y + x^2*y^2 - x*y^3 - y^4 + 2*x^3*z + 2*x^2*y*z - 2*x*y^2*z - y^3*z + 2*x^2*z^2 + y^2*z^2 + x*z^3 + 2*y*z^3 + z^4;

curves := [C1, C2, C3, C4, C5];

// Map each curve to its list of <prime, <a1, a2, a3>> triples
triplesMap := [
    [ // C1
        <587, <567, 115, 309>>,
        <23603, <23308, 8189, 14451>>,
        <669607, <1697, 586968, 386345>>,
        <23396969, <23395640, 1853920, 16090702>>
    ],
    [ // C2
        <863, <834, 727, 732>>,
        <29131, <28, 1805, 3131>>,
        <766393, <765688, 160562, 338289>>,
        <19783627, <19781951, 9447733, 12223538>>
    ],
    [ // C3
        <659, <635, 252, 615>>,
        <21937, <123, 9752, 9646>>,
        <1018777, <40, 73731, 522152>>,
        <26032751, <26028995, 13783493, 19319107>>
    ],
    [ // C4
        <821, <13, 99, 24>>,
        <29027, <51, 5360, 21080>>,
        <796877, <795699, 356066, 198341>>,
        <21461053, <2374, 12009259, 6834612>>
    ],
    [ // C5
        <971, <949, 209, 484>>,
        <24391, <24261, 10049, 16941>>,
        <1045543, <1044836, 877165, 294273>>,
        <25587203, <25583766, 5208260, 23389010>>
    ]
];

runDemo := procedure()
    for i in [1..#curves] do
        fOverQ := curves[i];
        printf "\n--- Processing Curve %o ---\n", i;
        print fOverQ;
        
        for data in triplesMap[i] do
            p := data[1];
            lpolyModResults := data[2];

            f := ChangeRing(fOverQ, GF(p));
            printf "\nLifting at p = %o with [a1 mod p,a2 mod p,a3 mod p] = %o\n", p, lpolyModResults;

            start := Cputime();
            results := lPolyWrapper(fOverQ, f, p, lpolyModResults : method := "hybrid");
            assert #results eq 1;
            result := results[1];
            finish := Cputime();
            
            print "Result:", result;
            //print "Jacobian size over Fp", getJacSize(p, result[1], result[2], result[3]);
            //print "Jacobian size over Fp2", getJacSizeFp2(p, result[1], result[2], result[3]);
            printf "Time: %o seconds\n", finish - start;

        end for;
    end for;
end procedure;

runDemo();
