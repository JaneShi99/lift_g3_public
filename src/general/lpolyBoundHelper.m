/*
    Computing the a1, a2 (Weil bounds and KS bounds), a3 bounds
*/
computeA1Bounds := function(p)
    return <-6*Sqrt(p), 6*Sqrt(p)>;
end function;

computeA2Bounds := function(p)
    return  <-15*p, 15*p>;
end function;

computeKSA2Bounds := function(p, a1)
    upperBound := 3*p + (a1^2)/3;
    deltaHelper := Round((a1/Sqrt(p))/4) * 4;
    delta := Abs(deltaHelper - (a1/Sqrt(p)));
    lowerBound := -p + (a1^2 - p*delta^2)/2;
    return <lowerBound, upperBound>;
end function;

computeA3Bounds := function(p)
    return <-20*p^(3/2), 20*p^(3/2)>;
end function;


/*
Generate candidates within the bounds 
given the residues
*/
CandidatesWithinBounds := function(residue, p, lowerBound, upperBound)

    modRep := Integers()!((Integers()!residue) mod p);
    //print modRep, p;
    assert (0 le modRep) and (modRep lt p);

    lowerCandidate := Ceiling((lowerBound-modRep)/p)*p+modRep;
    upperCandidate := Floor((upperBound-modRep)/p)*p+modRep;

    assert lowerCandidate mod p eq modRep;
    assert upperCandidate mod p eq modRep;
    assert lowerCandidate-p lt lowerBound;
    assert upperCandidate+p gt upperBound;

    candidateSize :=(((upperCandidate-lowerCandidate)/p)+1);
    assert Denominator(candidateSize) eq 1;
    candidateSize := Numerator(candidateSize);
    candidates := [lowerCandidate + p*i : i in [0..candidateSize-1]];
    
    return candidates;
end function;

/*
When p\geq 144, there's only one possibility for a1.
*/
GetA1Pbig := function(p, a1modp)
    assert p gt 144;

    a1:=Integers()! (Integers()! (a1modp) mod p);
    
    assert 0 le a1 and a1 lt p;
    return (a1 gt p/2) select a1-p else a1;
end function;

/*
Get all possible [a1,a2] pairs within bounds
*/
GetA1A2Candidates := function(a1modp, a2modp, p)
    a1Candidates := (p lt 144) select (CandidatesWithinBounds(a1modp, p, c[1], c[2]) where c is computeA1Bounds(p)) else [GetA1Pbig(p, a1modp)];
    results := [];
    for a1 in a1Candidates do
        a2Bounds := computeKSA2Bounds(p,a1);
        //print "a1, a2bounds, a2boundSize", a1,a2Bounds, a2Bounds[2]-a2Bounds[1];
        for a2 in CandidatesWithinBounds(a2modp, p, a2Bounds[1],a2Bounds[2]) do
            Append(~results, [a1,a2]);
        end for;
    end for;

    assert #results ge 1;
   return results;
end function;


getJacSize := function(p, a1, a2, a3)
    return p^3 + a1*p^2 + a2*p + a3 + a2 + a1 + 1;
end function;


getJacSizeFp2 := function(p, a1, a2, a3)
    return (p^3 + a1*p^2 + a2*p + a3 + a2 + a1 + 1)*(p^3 - a1*p^2 + a2*p - a3 + a2 - a1 + 1);
end function;

getJacSizeFp3 := function(p, a1, a2, a3)
    R<T> := PolynomialRing(Integers());
    L := p^3*T^6 + a1*p^2*T^5 + a2*p*T^4 + a3*T^3 + a2*T^2 + a1*T + 1;
    return Resultant(L, T^3 - 1);
end function;

getJacQuotientSize := function(p, a1, a2, a3)
    q := getJacSizeFp2(p, a1, a2, a3)/getJacSize(p, a1, a2, a3);
    assert IsIntegral(q);
    return Integers()!q;
end function;
/*
This is a namedTuple that returns the lpolymod and bound info conveniently.
*/
lPolyModBoundInfo := recformat<
    a1a2Pairs,
    a3Min,
    a3Max
>;

getLpolyModBoundInfo := function(fOverQ, p, lpolyModResults)

    a1modp, a2modp, a3modp := Explode(lpolyModResults); 
    a1a2Pairs := GetA1A2Candidates(a1modp, a2modp, p);
    a3Candidates := CandidatesWithinBounds(a3modp, p, c[1],c[2]) where c is computeA3Bounds(p);

    info := rec<lPolyModBoundInfo |
        a1a2Pairs := a1a2Pairs,
        a3Min := Min(a3Candidates),
        a3Max := Max(a3Candidates)
    >;

    return info;
end function;

