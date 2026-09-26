/*
This file combines g3 group code and uses lpolyhelper code 
to compute l-poly
*/


AttachSpec("./src/g3/g3Naive.spec");
AttachSpec("./src/g3/g3Hybrid.spec");
load "./src/general/lpolyBoundHelper.m";

/*
Computes the size of the giant/baby steps
*/
computeStepSize := function(p)
    return Ceiling(Sqrt(40)*(p^(1/4)));
end function;


associativeArrayPrint := procedure(Arr)
    for k in Keys(Arr) do
        print "key = ", k;
        print "values", Arr[k];
    end for;
end procedure;

/*
magma implementation of defaultdict(set) 
*/
addToDict := procedure(~AA, key, value)
    if not IsDefined(AA, key) then 
        AA[key] := {};
    end if;
    Include(~AA[key],value);
end procedure;

/*
This is the overall wrapper to compute l-poly
For the indexing for BSGS, see the paper.
*/

lPolyWrapper := function(fOverQ, f, p, lpolymodResults : method := "hybrid", a2Indicator := false, a2Value := 0)

    assert p gt 127;
    assert method in ["naive", "hybrid", "hyperelliptic"];
    
    // Setup the l-poly info: a1 mod p, a2 mod p, a3 mod p,
    // as well as the intervals for a1, a2, a3

    lPolyModBoundInfo := getLpolyModBoundInfo(fOverQ, p, lpolymodResults);
    a1a2Pairs := lPolyModBoundInfo`a1a2Pairs;
    assert #a1a2Pairs gt 0;
    a3Min := lPolyModBoundInfo`a3Min;
    a3Max := lPolyModBoundInfo`a3Max;

    if a2Indicator then 
        a1a2Pairs := [a1a2Pair : a1a2Pair in a1a2Pairs | a1a2Pair[2] eq a2Value];
    end if;

    //print lPolyModBoundInfo;

    // set up the BSGS in Jac(f).
    r := computeStepSize(p);
    s := computeStepSize(p);

    if method eq "naive" then 
        J := G3JacNaiveCreation(f);
    elif method eq "hybrid" then
        J := G3JacHybridCreation(f);
    else 
        // hyperelliptic
        J := Jacobian(HyperellipticCurve(f));
    end if;

    anniToTriple := AssociativeArray();

    if method eq "naive" or method eq "hybrid" then 
        D :=  generateGeneralPoint(J);
    else 
        // hyperelliptic
        D :=  Random(J);
    end if;


    for a1a2Pair in a1a2Pairs do 
        a1, a2 := Explode(a1a2Pair);    

        ell := (p^3+1) + a1*(p^2+1) + a2*(p+1);

        babyStepsToIndex := AssociativeArray();

        pD := p * D;
        rpD := (p*r) * D;

        babyAcc := 0 * D;
        
        babyAccHash := (method eq "naive" or method eq "hybrid") select babyAcc`hash else babyAcc;

        babyStepsToIndex[babyAccHash] := 0;

        for babyIndex in [1..r] do 
            babyAcc := babyAcc + pD;
            babyAccHash := (method eq "naive" or method eq "hybrid") select babyAcc`hash else babyAcc;
            babyStepsToIndex[babyAccHash] := babyIndex * p;
        end for;

        ellMin := ell + a3Min;
        giantAcc := ellMin * D;
        giantAccHash := (method eq "naive" or method eq "hybrid") select giantAcc`hash else giantAcc;
        if IsDefined(babyStepsToIndex, giantAccHash) then  
            babyIndex := babyStepsToIndex[giantAccHash];
            a3 := -babyIndex;
            addToDict(~anniToTriple, ellMin-babyIndex, [a1,a2,a3]);
        end if;

        for giantIndex in [1..(s+1)] do 
            giantAcc := giantAcc + rpD;
            giantAccHash := (method eq "naive" or method eq "hybrid") select giantAcc`hash else giantAcc;
            if IsDefined(babyStepsToIndex, giantAccHash) then  
                babyIndex := babyStepsToIndex[giantAccHash];
                anni := ellMin + giantIndex*r*p - babyIndex;
                a3 := anni - ell;
                if a3Min le a3 and a3 le a3Max then
                    addToDict(~anniToTriple, anni, [a1,a2,a3]);
                end if;
            end if;
        end for;
    end for;

    /*
    if method eq "hybrid" then 
        print "Addition data";
        //print J`TESTAdditionLog;
        print "Total naive adds", J`TESTNaiveAddCount;
        print "Total naive time", J`TESTNaiveAddTime;
        print "Total typical adds", J`TESTTypicalAddCount;
        print "Total typical time", J`TESTTypicalAddTime;
    end if;
    */
    
    //print "Here is the collisions table!";
    //associativeArrayPrint(anniToTriple);

    allTriples := &cat[Setseq(anniToTriple[k]): k in Keys(anniToTriple)];
    //print allTriples;

    // if only one triple remains, it must be the answer. If no triples 
    // remains, we must have implemented the algorithm incorrectly.
    if #allTriples eq 0 then
        assert false;
    end if;

    if #allTriples eq 1 then 
        return allTriples;
    end if;

    // now, if multiple triples remain, then 
    // compute the sizes in $Jac(f \times F_{p^2})$
    // No need to use BSGS at this point, linear search
    // is enough as there is a small number of candidates left.


    if method eq "naive" then 
        J2 := G3JacNaiveCreation(ChangeRing(f, GF(p^2)));
    elif method eq "hybrid" then 
        J2 := G3JacHybridCreation(ChangeRing(f, GF(p^2)));
    elif method eq "hyperelliptic" then
        J2 := Jacobian(HyperellipticCurve(ChangeRing(f, GF(p^2))));
    else 
        assert false;
    end if;

    finalTriples := [];

    if method eq "hyperelliptic" then 
        D2 := Random(J2);
    else 
        D2 := generateGeneralPoint(J2);
    end if;

    for t in allTriples do 
        J2Size := getJacSizeFp2(p,t[1],t[2],t[3]);
        JSize := getJacSize(p, t[1], t[2], t[3]);
        assert J2Size mod JSize eq 0;
        JTwistSize := J2Size div JSize;
        

        finalPt := JTwistSize * D2;

        // finalPt lies in J(F_p) iff it is fixed by the p-power Frobenius.
        // Checking that the support points have F_p coordinates is not enough:
        // a divisor over F_p can be supported on Galois orbits over F_(p^2), F_(p^3).
        // Here, need three methods: "naive, hybrid, or hyperelliptic"
        // TODO: implement this to naive and hyperelliptic
        if finalPt eq Frobenius(finalPt) then
            Append(~finalTriples, t);
        end if;
    end for;

    return finalTriples;


end function;