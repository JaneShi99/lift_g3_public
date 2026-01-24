import "./g3utils.m": 
    translateStandard,
    pointBaseCoerce,
    magmaSetupHelper,
    createHash,
    typicalAddition,
    naiveAddition,
    uvIsValid,
    checkConvertibleToTypical,
    tangentLineThroughCurvePoint,
    curveThroughPtsWithTangent,
    groebnerMethod,
    intersectionDataToMultiset;

quarticCoeffs := recformat<
    dehomf,
    h1,
    h2,
    f4
>;

declare type G3JacNaive;
/*
Note: G3Hybrid is a wrapper that says: whenever two points to be added are typical,
outsource to Ritzenhaler's code. Otherwise use our usual naive code.
So it entirely depends on g3Naive.

Note: G3Smart is completely standalone from G3Naive and G3Hybrid.
*/

declare type G3JacHybrid;
declare attributes G3JacHybrid:
    //------------------------------  following attributes are common to all three Jacobian implementations.
    Standardf, // f that defines the genus 3 curve, degree 4 homogenous polynomial in x,y,z in GF(q). This is after the transformation
    MagmaIndicator, // the constructor by default sets it to false. If it's set to true, then it uses magma's built-in function to update the lpoly/order below
    MagmaLpolyCheck, // use magma's built-in function to get its l-poly
    MagmaOrder, // use magma's built-in function to get its order
    BaseField, //GF(q)
    BaseSpace, //Projective space over (BaseField)
    ExtendedStandardf, // f base changed to GF(q^6)
    mumfordInfo, //dehomf, h1, h2, h4 as Ritzenhaler's code
    //------------------------------  following attributes are only common to G3JacNaive and G3Jac
    Identity, //G3JacNaivePoint type object with P1Inf + P2Inf + P3Inf
    ExtendedField, //GF(q^6)
    ExtendedSpace,//Projective space over (ExtendedField)
    //----------------------------- following are defined differently for different implementation of jacobians
    LInf, // line that intersects f at 4 rational points, with intersection pts (2,1,1). default z=0
    P1Inf, // (0:1:0) point on LInf
    P2Inf, // (0:1:0) point on LInf
    P3Inf, // (x:y:0) point on LInf
    P4Inf, // (1:0:0) point on Linf
    QuarticCoeffs,
    TESTTypicalAddCount,
    TESTNaiveAddCount,
    TESTTypicalAddTime,
    TESTNaiveAddTime,
    TESTAdditionLog;

declare type uvData;

declare attributes uvData:
    u, //a polynomial in F_q, degree 2 or 3
    v; //a polynomial in F_q, degree 0, 1 or 2 or 3 

declare type G3JacHybridPoint;
declare attributes G3JacHybridPoint:
    Parent, //type G3JacHybrid object
    TypicalFlag, //typical or not
    D, //the D data if Naive
    uvData, //type uvdata
    hash; //hash


intrinsic uvDataCreation(u::RngMPolElt,v::RngMPolElt) -> uvData
{creates uv point}
    UV := New(uvData);
    UV`u := u;
    UV`v := v;
    return UV;
end intrinsic;


/*
G3JacHybridPoint constructor in the typical case
*/
intrinsic G3JacHybridPointCreation(J::G3JacHybrid, UV::uvData) -> G3JacHybridPoint
{Creates a typical divisor}
    assert uvIsValid(UV`u, UV`v);
    JP := New(G3JacHybridPoint);
    JP`Parent := J;
    JP`TypicalFlag := true;
    JP`uvData := UV;
    JP`hash := "T|" cat Sprint(UV`u) cat "|" cat Sprint(UV`v);
    return JP;
end intrinsic;


/*
G3JacHybridPoint constructor in the atypical case
*/
intrinsic G3JacHybridPointCreation(J::G3JacHybrid, P1::Pt, P2::Pt, P3::Pt) -> G3JacHybridPoint
{Takes Jacobian J and three points}
    JP := New(G3JacHybridPoint);
    JP`Parent := J;
    JP`TypicalFlag := false;
    // Remove the dependency from g3Naive ONCE IN FOR ALL
    JP`D := {*P1,P2,P3*};
    //JP`hash := <"N", createHash(JP`D,J)>;
    // potential problem: Sprint for multiset is not unique?
    JP`hash := "N|" cat Sprint(JP`D);
    return JP;
end intrinsic;

/*
obtais the coefficients needed for Ritzenhaler's implementation
*/

getHs := function(f)
    R := Parent(f);
    q := #BaseRing(R);
    
    A2<X,Y>:=PolynomialRing(GF(q),2);
    dehomf := Evaluate(f,[X,Y,1]);

    /* Coefficient in front of those must be zero or 1 */
    zeroMonomials := [X^4, Y^4, Y^3*X];
    monicMonomial := [Y^3];

    assert &and[MonomialCoefficient(dehomf, monomial) eq 0: monomial in zeroMonomials];
    assert &and[MonomialCoefficient(dehomf, monomial) eq 1: monomial in monicMonomial];

    h1 := Coefficient(dehomf, Y, 2);  
    h2 := Coefficient(dehomf, Y, 1);  
    f4 := -Coefficient(dehomf, Y, 0); 

    info := rec<quarticCoeffs | 
        dehomf := dehomf,
        h1 := h1,
        h2 := h2,
        f4 := f4
    >;

    return info;

end function;

/*
Constructor for G3JacHybrid object

If setupMagma flag is set to true, then it uses magma to compute l-poly.
Then it translates f so that its rational intersection number with line l=z is (2,1,1)
Lastly, it sets its identity.
*/

intrinsic G3JacHybridCreation(definingEquation::RngMPolElt) -> G3JacHybrid
{Takes a polynomial of defined in GF(q)[x,y,z] or GF(q^2)[x,y,z] and make it 
into type G3JacHybrid}
    //printf "G3 Creation called!!!\n";
    //Setup basic attributes code
    J := New(G3JacHybrid);
    q := #BaseRing(Parent(definingEquation));
    J`BaseField := GF(q);
    Proj2<x,y,z> := ProjectiveSpace(GF(q),2);
    J`BaseSpace := Proj2;

    // Though the basefield could be an extension of GF(p), we would 
    // like the standard f still be defined in GF(p)

    p := Characteristic(J`BaseField);
    pField := GF(p);
    pSpace := ProjectiveSpace(GF(p),2);

    // Translate everything to prime field and obtain the translated equation
    pEquation := ChangeRing(definingEquation, pField);
    pfStandard, plInf, pP1234 := translateStandard(pEquation, pSpace, pField);

    // Coerce outputs back to GF(q)
    baseRing := PolynomialRing(GF(q), 3);
    J`Standardf := baseRing!pfStandard;
    J`LInf := baseRing!plInf;
    P1234 := [Proj2![GF(q)!coord : coord in [P[1], P[2], P[3]]] : P in pP1234];

    J`ExtendedField := GF(q^6);
    Proj2Ext<u,v,w> := ProjectiveSpace(GF(q^6), 2);
    J`ExtendedSpace := Proj2Ext;
    J`ExtendedStandardf := Evaluate(J`Standardf,[u,v,w]);

    // Define P1,P2,P3,P4 in extended field
    J`P1Inf := pointBaseCoerce(P1234[1],Proj2Ext);
    J`P2Inf := pointBaseCoerce(P1234[2],Proj2Ext);
    J`P3Inf := pointBaseCoerce(P1234[3],Proj2Ext);
    J`P4Inf := pointBaseCoerce(P1234[4],Proj2Ext);


    //Setup identity
    J`Identity := G3JacHybridPointCreation(J, J`P1Inf, J`P2Inf, J`P3Inf);


    // Setup things for record.
    J`TESTTypicalAddCount := 0; // testing purpose only: it counts number of times typical addition is used
    J`TESTNaiveAddCount := 0;  //testing purpose only: it counts number of times naive addition is used
    J`TESTTypicalAddTime := 0;  // testing purpose only: total time on typical addition
    J`TESTNaiveAddTime := 0;  //testing purpose only: total time on naive addition
    //Sanity check
    //assert (J`Identity + J`Identity)`D eq (J`Identity)`D;
    J`QuarticCoeffs := getHs(J`Standardf);
    J`TESTAdditionLog := [];

    return J;
end intrinsic;


intrinsic Print(J::G3JacHybrid){}
	printf "Jacobian whose standard curve defined by %o\n", J`Standardf;
    printf "in base field %o\n", J`BaseField;
    printf "with intersecting line %o\n", J`LInf;
    printf "with P1 = %o, P2 = %o, P3 = %o, P4 = %o\n", J`P1Inf, J`P2Inf, J`P3Inf, J`P4Inf;
    printf "in base projective space %o and \n extended projective space %o\n", J`BaseSpace, J`ExtendedSpace;
    printf "with quartic coefficients %o\n", J`QuarticCoeffs;
end intrinsic;

intrinsic Print(uv::uvData){}
    printf "u = %o, v = %o", uv`u, uv`v;
end intrinsic;


intrinsic Print(P::G3JacHybridPoint){}
    if P`TypicalFlag then 
    printf "Typical point with uv data %o\n", P`uvData;
    else 
    printf "Atypical point with D data %o\n", P`D;
    end if;
end intrinsic;


/*
Given a sequence of points,
return polynomial u,v such that 
x_i are roots of u and y_i = v(x_i)
*/
polyInterpolation := function(R, pts)

    X := R.1; Y := R.2;
    v := 0;

    for index in [1..#pts] do 
        skippedPoint := pts[index]; 
        remainingPoints := [pt: pt in pts | pt ne skippedPoint];

        Xi, Yi := Explode(skippedPoint);
        v +:= Yi * &*[(X-coord[1])/(Xi-coord[1]): coord in remainingPoints];
    end for;
    u := &*[X-coord[1]: coord in pts];
    return <u,v>;

end function;

generateThreeRandomPoints := function(dehomf)
    maxTries := 10000;
    R := Parent(dehomf);
    q := #BaseRing(R);
    X := R.1; Y:= R.2; 

    seen := {};
    it := 0;
    while it lt maxTries and #seen lt 3 do
        XCoord:= Random(GF(q));
        YRoots := Roots(UnivariatePolynomial(Evaluate(dehomf,[XCoord,Y])));
        if #YRoots ge 1 and not XCoord in [pt[1]: pt in seen] then
            YCoord := Random([factor[1]: factor in YRoots]);
            Include(~seen, [XCoord,YCoord]);
            it +:= 1;
        end if;
    end while;
    threePoints := Setseq(seen);
    return threePoints;
end function;

/*
Given dehomogenized f, generate 
points on Jac(C) in mumford representation
*/
generateMumfordPoints := function(dehomf)

    foundValidUv := false;

    while not foundValidUv do
        threePoints := generateThreeRandomPoints(dehomf);
        R := Parent(dehomf);
        //print "parent of dehom is:::::: ", R;
        u, v := Explode(polyInterpolation(R, threePoints));
        if uvIsValid(u,v) then 
            foundValidUv := true;
        end if;
    end while;

    res := uvDataCreation(u,v);
    return res;
end function;

intrinsic generateGeneralPoint(J::G3JacHybrid)->G3JacHybridPoint
{Generate a random typical point}
    dehomf := J`QuarticCoeffs`dehomf;
    uv := generateMumfordPoints(dehomf);

    P := G3JacHybridPointCreation(J, uv);
    return P;
end intrinsic;


typicalToPts := function(D)
    typicalRep := D`uvData;
    u := typicalRep`u;
    v := typicalRep`v;
    J := D`Parent;
    extField := J`ExtendedField;

    uExt := ChangeRing(u, extField);
    vExt := ChangeRing(v, extField);

    xs := [r[1]: r in Roots(UnivariatePolynomial(uExt))];
    //printf "xs %o\n", xs;
    assert #xs eq 3;
    xys := [<x,Evaluate(UnivariatePolynomial(vExt), x)> : x in xs];
    pts := {* J`ExtendedSpace![xy[1], xy[2], extField!1]: xy in xys *};
    
    return pts;
end function;

ptsToUV := function(Pts, resultPolyRing)//, ResultFieldOfDefn
    RExt := PolynomialRing(Parent(Pts[1][1]), 2);
    xys := [[Pt[1],Pt[2]]: Pt in Pts];
    uvExtField := polyInterpolation(RExt, xys);

    uExt := uvExtField[1];
    vExt := uvExtField[2];

    uExtUni := UnivariatePolynomial(uExt);
    vExtUni := UnivariatePolynomial(vExt);

    assert Degree(uExtUni) eq 3 and IsMonic(uExtUni);
    assert Degree(vExtUni) eq 2;

    X := resultPolyRing.1;
    resultField := BaseRing(resultPolyRing);
    u := &+[X^i * resultField!Coefficient(uExtUni,i) : i in [0..3]];
    v := &+[X^i * resultField!Coefficient(vExtUni,i) : i in [0..2]]; 
    
    return <u,v>;

end function;


intrinsic '+'(D1::G3JacHybridPoint, D2::G3JacHybridPoint)->G3JacHybridPoint
{add point using typical addition, if anything fails fall back to naive impl}
    J := D1`Parent;
    quarticCoeffs := J`QuarticCoeffs;

    if not D1`TypicalFlag then 
        if D1`D eq J`Identity`D then 
            return D2;
        end if;
    end if;

    if not D2`TypicalFlag then 
        if D2`D eq J`Identity`D then 
            return D1;
        end if;
    end if;


    if D1`TypicalFlag and D2`TypicalFlag then 
        try 
            typicalStartTime := Cputime();
            D3uv := typicalAddition(quarticCoeffs, D1`uvData, D2`uvData);
            D3uvData := uvDataCreation(D3uv[1],D3uv[2]);
            typicalFinishTime := Cputime();
        catch e 
            ;
            //printf "In catch handler\n";
            //printf "Trying to add %o, %o\n", D1, D2;
            //printf "Error calling procedure with parameter: %o\n", e`Object;
        end try;

        if assigned D3uvData then 
            D3 := G3JacHybridPointCreation(J, D3uvData);
            //printf "Degree of u:%o\n", Degree(UnivariatePolynomial(D3uv[1]));
            J`TESTTypicalAddCount +:= 1;
            Append(~J`TESTAdditionLog, "Typical");
            J`TESTTypicalAddTime +:= typicalFinishTime - typicalStartTime;
            return D3;
        end if;
    end if;

    //If we reach this step, that means either 1. not both are typical or 2. typical addition has failed.
    //printf "Now we're doing naive addition. \n";

    naiveStartTime := Cputime();
    if D1`TypicalFlag then 
        D1NaiveRep := typicalToPts(D1);
    else 
        D1NaiveRep := D1`D;
    end if;

    if D2`TypicalFlag then 
        D2NaiveRep := typicalToPts(D2);
    else 
        D2NaiveRep := D2`D;
    end if;

    //Now we're doing the naive addition. We can do this with certainty.
    DPts := naiveAddition(J`ExtendedStandardf, J`ExtendedSpace, D1NaiveRep, D2NaiveRep, J`P1Inf, J`P2Inf, J`P3Inf, J`P4Inf);

    //printf "Done naive +\n\n";
    convertibleToTypical := checkConvertibleToTypical(DPts);

    //print "---------------------------------\n";
    //print DPts;
    //printf "Testing uv-convertible: %o\n", convertibleToTypical;
    naiveEndTime := Cputime();

    J`TESTNaiveAddCount +:= 1;
    Append(~J`TESTAdditionLog, "Naive");
    J`TESTNaiveAddTime +:= naiveEndTime - naiveStartTime;
    if convertibleToTypical then 
        basePolyRing := Parent(J`QuarticCoeffs`dehomf);
        uvDataRaw := ptsToUV(DPts, basePolyRing);
        uvData := uvDataCreation(uvDataRaw[1], uvDataRaw[2]);
        return G3JacHybridPointCreation(J, uvData);
        //printf "Converted";
    else 
        return G3JacHybridPointCreation(J, DPts[1], DPts[2], DPts[3]);
    end if;

end intrinsic;


intrinsic '*'(n::RngIntElt, D::G3JacHybridPoint)->G3JacHybridPoint 
{double and add using addition}
    assert n ge 0;
    if n eq 0 then
        return (D`Parent)`Identity;
    end if;
    Acc := D;
    binString := Reverse(Intseq(n,2));
    divisorsAlongWay := [];
    for idx in [2..#binString] do    
        d := binString[idx];
        //printf "Doubling...\n";
        Acc := Acc + Acc;
        if d eq 1 then 
            //printf "Adding...\n";
            Acc := Acc + D;
        end if;
        //printf "Iteration number%o\n of %o\n", idx, #binString;
        Append(~divisorsAlongWay, Acc);
    end for;

    //print "divisorsAlongWay",divisorsAlongWay;
    return Acc;

end intrinsic;


// TODO: this negation is the same as the naive negation. wrap it in a
// function inside utils 
/*
Computes the negation of a point. See paper for details.
*/
intrinsic '-'(D1::G3JacHybridPoint)-> G3JacHybridPoint
{compute the negation of a point}
    J := D1`Parent;
    f := J`ExtendedStandardf;
    Proj2Ext := J`ExtendedSpace;

    if D1`TypicalFlag then 
        D1NaiveRep := typicalToPts(D1);
    else 
        D1NaiveRep := D1`D;
    end if;

    D1, D2, D3 := Explode([P: P in D1NaiveRep]);

    listOfPoints := [D1,D2,D3,J`P4Inf,J`P4Inf];
    multisetPoints := {*P: P in listOfPoints*};
    setPoints := Set(listOfPoints);

    if &and[Multiplicity(multisetPoints, P)lt 3: P in setPoints] then
        PointTangentPairs := [ <P, tangentLineThroughCurvePoint(f,P, Proj2Ext)>: P in setPoints |Multiplicity(multisetPoints,P) gt 1];
        quadric := curveThroughPtsWithTangent(listOfPoints, PointTangentPairs, 5, Proj2Ext);
    else 
        quadric := groebnerMethod(listOfPoints, f, 2, Proj2Ext);
    end if;
    
    //printf "\n quadric is %o\n",quadric;

    DDOTCdata := IntersectionNumbers(Curve(Proj2Ext, quadric), Curve(Proj2Ext, f));
    DDOTC := intersectionDataToMultiset(DDOTCdata);

    assert #DDOTC eq 8;
    assert Multiset(listOfPoints) subset DDOTC;
    D4Pts := [P: P in (DDOTC diff Multiset(listOfPoints))];

    DInv := G3JacHybridPointCreation(J, D4Pts[1],D4Pts[2],D4Pts[3]);
    return DInv;
end intrinsic;


intrinsic '-'(D1::G3JacHybridPoint, D2::G3JacHybridPoint)-> G3JacHybridPoint
{compute the difference of two points}
    return D1 + (-D2);
end intrinsic;

intrinsic checkIsId(D1::G3JacHybridPoint)->BoolElt
{check if a point is identity}
    return D1`TypicalFlag eq false and D1`D eq ((D1`Parent)`Identity)`D;
end intrinsic;
