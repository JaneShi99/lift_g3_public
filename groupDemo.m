AttachSpec("./src/g3/g3Hybrid.spec");
AttachSpec("./src/g3/g3Naive.spec");


P2<x,y,z> := ProjectiveSpace(Rationals(), 2);

C1 := x^2*y^2 + 2*x*y^3 + y^4 + x^3*z + x^2*y*z + x*y^2*z + x^2*z^2 - 2*x*y*z^2 - 2*x*z^3 - y*z^3 - z^4;
C2 := x^2*y^2 + x*y^3 + x^3*z + x*y^2*z + y^3*z - x^2*z^2 - 3*x*y*z^2 + 2*y^2*z^2 + x*z^3;
C3 := x*y^3 + x^3*z + 2*x*y^2*z + y^3*z - y*z^3 - z^4;

curves := [C1, C2, C3];

triplesMap := [
    [ // C1
        <587, 196110648>,
        <587^2, 41169356152777152>,
        <23396969, 12807198206523571984176>,
        <23396969^2, 164042960852775354416121999078156598004631744>
    ],
    [ // C2
        <863, 622457441>,
        <863^2, 414408121799141375>,
        <19783627, 7742495129264453801271>,
        <19783627^2, 59956388558598896340404804808737718933531543>
    ],
    [ // C3
        <659, 276349199>,
        <659^2, 82140842358569519>,
        <26032751, 17639956952618383447102>,
        <26032751^2, 311257884780401271455234907753783526110183740>
    ]
];

runDemo := procedure()
    for i in [1..#curves] do
        fOverQ := curves[i];
        printf "\n--- Working on Curve %o ---\n\n", i;
        print fOverQ;
        
        for data in triplesMap[i] do
            printf "q = %o\n", data[1];
            q := data[1];
            jacFqSize := data[2];

            f := ChangeRing(fOverQ, GF(q));   


            for i in [1,2] do

                style := (i eq 1) select "Hybrid" else "Naive";

                if style eq "Hybrid" then
                    J := G3JacHybridCreation(f);
                else
                    J := G3JacNaiveCreation(f);
                end if;

                rand1 := generateGeneralPoint(J);
                rand2 := generateGeneralPoint(J);

                start := Cputime();
                result := jacFqSize * (rand1 - rand2);
                
                assert checkIsId(result);

                finish := Cputime();
                printf "%o passed the test in %o seconds\n", style, finish - start;
                if style eq "Hybrid" then
                    printf "Had to use Naive adds %o times\n", J`TESTNaiveAddCount;
                    printf "---\n"; 
                end if;
            end for;
            
            print "----------------------\n";
        end for;
    end for;
end procedure; 

runDemo();
