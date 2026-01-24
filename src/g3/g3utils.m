/*
    Take the output of IntersectionNumbers <[P1,n1]...[Pk,nk]>
    and output multiset of the form {*P1 n1 times, ..., Pk nk times*}
*/
intersectionDataToMultiset := function(intData)
    return Multiset(&cat[[Tup[1]:i in [1..Tup[2]]]: Tup in intData]);
end function;


/*
f is a homogenous function in x,y,z, and P is on f.
Find the line tangent to f at P.
*/
tangentLineThroughCurvePoint := function(f, P, Proj2)
    R := Parent(f);
    x := R.1; y:= R.2; z:=R.3;

    xP := P[1];
    yP := P[2];
    zP := P[3];

    dfdx := Derivative(f, x);
    dfdy := Derivative(f, y);
    dfdz := Derivative(f, z);

    xCoeff := Evaluate(dfdx, [xP,yP,zP]);
    yCoeff := Evaluate(dfdy, [xP,yP,zP]);
    zCoeff := Evaluate(dfdz, [xP,yP,zP]);

    return xCoeff*x + yCoeff*y + zCoeff*z;

end function;


/*
returns the line in the 2-dimensional projective 
space that passes through P1 and P2

It uses sets up a linera system and looks at the kernel
*/

lineThroughPoints := function(P1, P2, Proj2)
    q := #BaseRing(Proj2);
    x := Proj2.1; y:= Proj2.2; z:=Proj2.3;

    monomials := [x,y,z];
    coefficients := [0: i in [1..#monomials]];
    monomialEvaluation := Matrix([[Evaluate(monomial, [P[1],P[2],P[3]]) : P in [P1,P2]]: monomial in monomials]);

    /*
    Note: Magma kernels are left kernels
    */

    coefficientBasis:= Basis(Kernel(monomialEvaluation));
    coeffs := coefficientBasis[1];
    return &+[monomials[i]*coeffs[i]: i in [1..#monomials]];
end function;




/*
returns whether three points are collinear.

If we get triple point, then see whether the tangent line intersects the point at least 3 times.
If two points are the same, then see if the third point is on the tangent line
of the first two points.
Otherwsie return whether they're collinear.
*/
threePointsCollinear := function(P1, P2, P3, f, Proj2)

    // triple point
    if (P1 eq P2) and (P2 eq P3) then 
        tangentLine := tangentLineThroughCurvePoint(f,P1,Proj2);
        LDOTCdata := IntersectionNumbers(Curve(Proj2, tangentLine), Curve(Proj2, f));
        LDOTC := intersectionDataToMultiset(LDOTCdata);
        return Multiplicity(LDOTC, P1) ge 3;
    end if;

    //double point
    if (P1 eq P2) or (P2 eq P3) or (P1 eq P3) then 
        if (P1 eq P2) then 
            tangentPoint := P1;
            otherPoint := P3;
        elif (P1 eq P3) then 
            tangentPoint := P1;
            otherPoint := P2;
        else
            tangentPoint := P2;
            otherPoint := P1;
        end if;
        
        tangentLine := tangentLineThroughCurvePoint(f, tangentPoint, Proj2);
        return Evaluate(tangentLine, [otherPoint[i]: i in [1,2,3]]) eq 0;

    end if;

    //three distinct points
    M := Matrix([[P[1], P[2], P[3]]: P in [P1,P2,P3]]);

    return Rank(M) lt 3;
end function;


/* 
Creates a hash function based on D. 
If three points are collinear, then it finds the line at which they're collinear.
Then, extrapolate the extra point using intersection numbers.
otherwise return the multiset
*/ 
createHash := function(D,J)
    P1, P2, P3 := Explode([P: P in D]);
    f := J`ExtendedStandardf;
    Proj2Ext := J`ExtendedSpace;

    if threePointsCollinear(P1,P2,P3,f,Proj2Ext) then 
        listOfPoints := [P1,P2,P3];
        multisetPoints := Multiset(listOfPoints);
        setPoints := Set(listOfPoints);

        if &or[Multiplicity(multisetPoints, P)gt 1: P in setPoints] then 
            doublePoint := [P: P in setPoints | (Multiplicity(multisetPoints, P) gt 1)][1];
            line := tangentLineThroughCurvePoint(f,doublePoint, Proj2Ext);
        else 
            line := lineThroughPoints(P1,P2,Proj2Ext); 
            //Something might be wrong with the above line:
            //it used to work with lineThroughPoints(P1,P2)
            //before the migration
        end if;

        LDOTCdata := IntersectionNumbers(Curve(Proj2Ext, line), Curve(Proj2Ext, f));
        LDOTC := intersectionDataToMultiset(LDOTCdata);
        
        assert #LDOTC eq 4;
        assert Multiset(listOfPoints) subset LDOTC;
        minusD := [P: P in (LDOTC diff Multiset(listOfPoints))][1];

        return Multiset([minusD]);
    else 
        return D;
    end if;
end function;


/*
Given smooth plane quartic f, find a line l such that it intersects f at four rational points,
with multiplicities (2,1,1). It also returns the coordinates of the double point and a single point.

It does so by finding tangent points P = (x,y,1), (to do this, enumerate x and solve for y),
then check whether the line tangent to C at P has the intersection multiplicity (1,1,2)
*/

findLine := function(f,Proj2, base)
    q := #base;
    R := Parent(f);
    x := R.1; y:= R.2; z:=R.3;
    oldCurve := Curve(Proj2, f);

    for xCoord in GF(q) do
        yCoordExpr := Roots(UnivariatePolynomial(Evaluate(f,[xCoord,y,1])));
        for yCoord in [factor[1]: factor in yCoordExpr] do 
            if Evaluate(f, [xCoord,yCoord,GF(q)!1]) eq 0 then
                tanLine := tangentLineThroughCurvePoint(f, Proj2!([xCoord,yCoord,GF(q)!1]), Proj2);
                //printf "line %o\n", tanLine;
                res := Resultant(f, tanLine, z);
                if {* factor[2] : factor in Factorization(res)*} eq {*1,1,2*} then
                    lineCurve := Curve(Proj2, tanLine);
                    intersectionData := IntersectionNumbers(oldCurve, lineCurve);
                    //printf "found a line with intersection 2,1,1\n";
                    singleIntersectionPoints := [data[1]: data in intersectionData| data[2] eq 1];
                    assert #singleIntersectionPoints eq 2;
                    newX1 := singleIntersectionPoints[1];
                    doubleIntersectionPoints := [data[1]: data in intersectionData| data[2] eq 2];
                    assert #doubleIntersectionPoints eq 1;
                    newX2 := doubleIntersectionPoints[1];
                    
                    lineFound := tanLine;

                    newX1Coords := [newX1[i]: i in [1,2,3]];
                    newX2Coords := [newX2[i]: i in [1,2,3]];
                    //printf "%o\n", intersectionData;

                    return lineFound, newX1Coords, newX2Coords;

                end if;
            end if;
        end for;
    end for;
end function;


/*

Given old-f, use the findLine function to find a line with rational intersection 
multiplicities (2,1,1),
and apply a linear change of variable to get f (new f), and l, such that
the intersection f and l is precisely
[* (1 : 0 : 0)^2, (0 : 1 : 0), (? : ? : 0), *]

This is used in the constructor.
*/
translateStandard := function(f,Proj2, base)
    oldCurve := Curve(Proj2, f);
    x := Proj2.1; y:= Proj2.2; z:=Proj2.3;
    lineFound, newX1Coords, newX2Coords := findLine(f,Proj2, base);

    /*
    We need to map P1 (newX1) (a point with trivial intersection), P2 (newX2) (tangent point) to [1,0,0], [0,1,0].
    To find the 3x3 translation matrix representing this linear change of variables,
    we define the matrices [newX1, newX2, unitvec]^T, where 
    unitvec vary in [[1,0,0],[0,1,0],[0,0,1]]. We pick whichever one is invertible 
    */
    unitVectorsInCorrectRing := [[base!P[1], base!P[2], base!P[3]]: P in [[1,0,0],[0,1,0],[0,0,1]]];
    possibleTranslationMatrices := [ Matrix([newX1Coords, newX2Coords, unit]): unit in unitVectorsInCorrectRing| not Determinant(Matrix([newX1Coords, newX2Coords, unit])) eq 0];

    assert #possibleTranslationMatrices ge 1;
    M := Transpose(possibleTranslationMatrices[1]);

    //printf "Translation matrix: %o\n", M;

    variableReplacement:=[
    M[1][1]*x+M[1][2]*y+M[1][3]*z, 
    M[2][1]*x+M[2][2]*y+M[2][3]*z, 
    M[3][1]*x+M[3][2]*y+M[3][3]*z];

    fNew := Evaluate(f, variableReplacement);

    /*
    The following assertion is here to make the coefficient of y^3 equal 1.
    We can make this assumption by non-singularity at (0:1:0)
    */
    y3Coeff := MonomialCoefficient(fNew, y^3*z);
    assert not (y3Coeff eq 0);
    fNew := fNew/y3Coeff;

    lNew := Evaluate(lineFound, variableReplacement);

    //printf "New intersection numbers: %o\n", IntersectionNumbers(Curve(Proj2, fNew), Curve(Proj2, lNew));
    intData := IntersectionNumbers(Curve(Proj2, fNew), Curve(Proj2, lNew));
    
    intDataMultiset := intersectionDataToMultiset(intData);

    P1 := Proj2![0,1,0];
    P2 := Proj2![0,1,0];
    P4 := Proj2![1,0,0];

    P1P2P4 := Multiset([Proj2![1,0,0],Proj2![0,1,0],Proj2![0,1,0]]);
    assert P1P2P4 subset intDataMultiset;

    P3 := [pt: pt in intDataMultiset diff P1P2P4][1];
    return fNew, lNew, [P1,P2,P3,P4];
end function;

/*
A helper function that takes a point and coerce it 
coordinate to coordinate into the desired projective space
*/

pointBaseCoerce := function(P, space)
    q := #BaseRing(space);
    newField := GF(q);
    //printf "%o %o %o", P[1], P[2], P[3];
    return space![newField!P[1], newField!P[2], newField!P[3]];
end function;




/*
assume that the multiplicities of L per point is at most 2.
(that is, there is no inflection point or flex points)
Then it finds a curve through a list of points with tangent

If numPts = 5 then we find a quadratic
If numPts = 9 then we find a cubic

It uses sets up a linera system and looks at the kernel
*/

curveThroughPtsWithTangent := function(L,tangenetPointLinePairs,numPts, Proj2)
    q := #BaseRing(Proj2);

    x := Proj2.1; y:= Proj2.2; z:=Proj2.3;
    
    assert numPts eq 5 or numPts eq 9;
    if numPts eq 9 then 
        monomials := [x^3, y^3, z^3, x^2*y, x*y^2, x^2*z, z^2*x, y^2*z, z^2*y, x*y*z];
    else 
        monomials := [x^2,y^2,z^2,x*y,x*z,y*z];
    end if;

    coefficients := [0: i in [1..#monomials]];
    monomialEvaluation := Matrix([[Evaluate(monomial, [P[1],P[2],P[3]]) : P in L]: monomial in monomials]);


    for tangentPointLinePair in tangenetPointLinePairs do 
        P := tangentPointLinePair[1];
        line := tangentPointLinePair[2];

        A:=GF(q)!Coefficient(line, x, 1);
        B:=GF(q)!Coefficient(line, y, 1);
        C:=GF(q)!Coefficient(line, z, 1);

        /*
        We know that the line given by (at P)
        (df/dx)x + (df/dy)y + (fd/dz)z = 0
        is the same as the line given by 
        Ax + By + Cz =0

        But we cannot go for the nullspace of 
        ((df/dx)-A) + ((df/dy)-B)y + ((fd/dz)-C)z = 0
        
        because there's an additional parameter for the projective space

        ((df/dx)-lambda*A) + ((df/dy)-lambda*B)y + ((fd/dz)-lambda*C)z = 0

        So, instead we add the following three conditions

        (df/dx)*B - (df/dy)*A=0
        (df/dx)*C - (df/dz)*A=0
        (df/dy)*C - (df/dz)*B=0
        */

        extraColumn1 := (Matrix([[Evaluate(Derivative(monomial,x),[P[1],P[2],P[3]])*B - Evaluate(Derivative(monomial,y),[P[1],P[2],P[3]])*A] : monomial in monomials]));
        extraColumn2 := (Matrix([[Evaluate(Derivative(monomial,x),[P[1],P[2],P[3]])*C - Evaluate(Derivative(monomial,z),[P[1],P[2],P[3]])*A] : monomial in monomials]));
        extraColumn3 := (Matrix([[Evaluate(Derivative(monomial,y),[P[1],P[2],P[3]])*C - Evaluate(Derivative(monomial,z),[P[1],P[2],P[3]])*B] : monomial in monomials]));
        
        monomialEvaluation := HorizontalJoin(monomialEvaluation, extraColumn1);
        monomialEvaluation := HorizontalJoin(monomialEvaluation, extraColumn2);
        monomialEvaluation := HorizontalJoin(monomialEvaluation, extraColumn3);
    end for;

    /*
    Note: Magma kernels are left kernels
    */

    coefficientBasis:= Basis(Kernel(monomialEvaluation));
    coeffs := coefficientBasis[1];
    return &+[monomials[i]*coeffs[i]: i in [1..#monomials]];
end function;

/*
Check whether all the point in the array points are 
moved into the affine patch z \neq 0.
This function is used after linear change of variables
*/
successfullyMoveZAffinePatch := function(points, M, Proj2)
    q:=#BaseRing(Proj2);
    return &and[not Pvec[3] eq 0 where Pvec := M*Matrix([[GF(q)!P[1]],[GF(q)!P[2]],[GF(q)!P[3]]]): P in points];
end function;

/*
Perform a linear transformation of variables to all the points in 
the list points
*/
linearTransformPoints := function(M, points, Proj2)
    q:=#BaseRing(Proj2);
    return [[Pvec[1][1],Pvec[2][1],Pvec[3][1]] where Pvec:=M*Matrix([[GF(q)!P[1]],[GF(q)!P[2]],[GF(q)!P[3]]]): P in points];
end function;

/*
Perform a linear transformation of variables a function in P^2
*/
linearTransformFunction := function(M, f, Proj2)
    M:=M^(-1);

    x := Proj2.1; y:= Proj2.2; z:=Proj2.3;

    VariableReplacement:=[
        M[1][1]*x+M[1][2]*y+M[1][3]*z, 
        M[2][1]*x+M[2][2]*y+M[2][3]*z, 
        M[3][1]*x+M[3][2]*y+M[3][3]*z];

    fTransformed := Evaluate(f, [v: v in VariableReplacement]);

    return fTransformed;
end function;

/*
Given a homogenized equation, de-homogenize 
at the third variable
*/
dehomogenizeAt3f := function(f,Proj2)
    q:= #BaseRing(Proj2);
    A2<X,Y>:=PolynomialRing(GF(q),2);
    return Evaluate(f, [X,Y,1]);
end function;

/*
Given a points [x,y,z] on the affine 
patch z=/=0 return [x/z,y/z]
*/
dehomogenizeAt3Points := function(points)
    assert &and[not IsZero(P[3]): P in points];
    Ldehom := [[P[1]/P[3], P[2]/P[3]]: P in points];
    return Ldehom;
end function;

/*
    homogenize function f at third variable
*/
homogenizefat3 := function(f, deg, Proj2);
    x := Proj2.1; y:= Proj2.2; z:=Proj2.3;
    homf:= Homogenization(Evaluate(f, [x,y]),z);
    assert Degree(homf) eq deg;
    return homf;
end function;


/*
Heuristics check: the story is the following:
the function curveThroughPointsGroebner yields multiple permissible cubics (quadratics),
and some are incorrect. To determine which ones are correct, 
we check the intersection number of this cubic (quadratics) and f and make sure it's the 
expected degree.

But it doesn't seem to be useful.
*/

/*
heuristicCheck := function(fdehom, candidatedehom, deg, degf, Proj2)

    candidateHom := homogenizefat3(candidatedehom,deg,Proj2);
    fHom := homogenizefat3(fdehom,degf,Proj2);
    intersectionData := IntersectionNumbers(Curve(Proj2, candidateHom), Curve(Proj2, fHom));
    printf "\n fhom %o", fHom;
    printf "\n candidateHom %o\n",candidateHom;
    printf "\n  #intersectionDataToMultiset(intersectionData)  %o\n", #intersectionDataToMultiset(intersectionData) ;
    return #intersectionDataToMultiset(intersectionData) eq deg*degf; 
end function;
*/

/*
Contrary to what the name suggests - this doesn't use 
groebner basis. Given points 
with multiplicities,it uses magma's ideal construction to find 
a curve of expected degree with prescribed points
*/
curveThroughPointsGroebner := function(f,points,expectDegree, Proj2)
    q:=#BaseRing(Proj2);
    A2<X,Y>:=PolynomialRing(GF(q),2);

    setOfPoints := Set(points);
    multisetOfPoints := Multiset(points);

    functionIdeal := ideal<A2 | f>;

    targetIdeal := &meet[Pideal^Multiplicity(multisetOfPoints, P) + functionIdeal where Pideal := ideal<A2 | X-P[1],Y-P[2]>: P in setOfPoints];
    //targetIdeal := &meet[Pideal^Multiplicity(multisetOfPoints, P) where Pideal := ideal<A2 | X-P[1],Y-P[2]>: P in setOfPoints];
    //print "--------------";
    //print targetIdeal;
    //print Basis(targetIdeal);

    //print "Groebner basis doesn't work?";
    //print GroebnerBasis(targetIdeal);

    correctDegreeIdeal := [basiselt: basiselt in Basis(targetIdeal) | Degree(basiselt) eq expectDegree];
    assert #correctDegreeIdeal ge 1;

    return correctDegreeIdeal[1];
end function;



/*
It finds a curve that intersects f at the set of points.

Transform to the affine patch z=/=0
then dehomogenize at z
then use grobener method to find curve,
then homogenize it back and translate back.
*/

groebnerMethod := function(points, f, deg, Proj2);
    q:=#BaseRing(Proj2);

    M := RandomMatrix(GF(q), 3, 3);
    while (Determinant(M) eq 0) or not successfullyMoveZAffinePatch(points, M, Proj2) do 
        M := RandomMatrix(GF(q), 3, 3);
    end while;

    Ltransformed := linearTransformPoints(M,points, Proj2);
    fTransformed := linearTransformFunction(M,f, Proj2);

    ldehom := dehomogenizeAt3Points(Ltransformed);
    fdehom := dehomogenizeAt3f(fTransformed, Proj2);

    g := curveThroughPointsGroebner(fdehom, ldehom,deg, Proj2);
    //print "Inside groebnber cubic******", g;
    gHom := homogenizefat3(g,deg,Proj2);

    gUntransformed := linearTransformFunction(M^(-1), gHom, Proj2);

    return gUntransformed;
end function;


/*
Generate a point on the curve f
where the Ps are distinct.

Note: the best way to do this is to encorporated galois orbits.
But at the time this function is written, we're still 
considering split in GF(p^6)

Note: J must be of G3JacNaive type
*/

generatekPoints := function(J, k)
    maxTries := 10000;
    it := 0;
    seen := {};
    q := #(J`BaseField);
    f := J`Standardf;
    R := Parent(f);
    x := R.1; y:= R.2; z:=R.3;

    Proj2Ext := J`ExtendedSpace;
    while it lt maxTries and #seen lt k do
        xCoord:= Random(GF(q));
        //printf "Roots y:%o\n", Evaluate(f,[xCoord,y,1]);
        yRoots := Roots(UnivariatePolynomial(Evaluate(f,[xCoord,y,1])));
        //printf "yRoots :%o\n", yRoots;
        if #yRoots ge 1 then
            yCoord := Random([factor[1]: factor in yRoots]);
            if Evaluate(f, [xCoord,yCoord,1]) eq 0 then
                Include(~seen, Proj2Ext![xCoord,yCoord,1]);
            end if;
            it +:= 1;
        end if;
    end while;
    assert #seen eq k;
    return Setseq(seen);
end function;

magmaSetupHelper := function(baseSpace, definingEquation)
    baseRing := BaseRing(baseSpace);
    deg := Degree(baseRing);

    if deg eq 1 then 
        return LPolynomial(Curve(baseSpace, definingEquation)); 
    // if degree is 2, we don't want to use magma's l-polynomial.
    // we rather get the l-polynomial over GF(p) and use an identity
    elif deg eq 2 then 
        p := Characteristic(baseRing);
        Fp := GF(p);

        tmpP2<a1,a2,a3> := ProjectiveSpace(Fp, 2);
        tmpR<a1,a2,a3> := CoordinateRing(tmpP2);

        tmpf := tmpR!definingEquation;

        C := Curve(tmpP2, tmpf);
        baseLPoly := LPolynomial(C);

        T := Parent(baseLPoly).1;
        polyDoubleDegree := baseLPoly * Evaluate(baseLPoly, -T);
        return &+[ Coefficient(polyDoubleDegree, 2*i) * T^i : i in [0..Degree(polyDoubleDegree) div 2] ];
    else
        error "Only supports prime degree = 1 or 2";
    end if;
end function;

naiveAddition := function(f, Proj2Ext, DAset, DBset, P1Inf, P2Inf, P3Inf, P4Inf)

    DAI1, DAI2, DAI3 := Explode([P: P in DAset]);
    DBI1, DBI2, DBI3 := Explode([P: P in DBset]);

    /*
    if {*DAI1, DAI2, DAI3*} eq {*P1Inf, P2Inf, P3Inf*} then 
        return <DBI1, DBI2, DBI3>;
    elif {*DBI1, DBI2, DBI3 *} eq {*P1Inf, P2Inf, P3Inf*} then 
        return <DAI1, DAI2, DAI3>;
    end if;
    */
    
    // Step 1. Find the cubic through the points
    listOfPoints := [DAI1, DAI2, DAI3, DBI1, DBI2, DBI3, P1Inf, P2Inf, P4Inf];
    multisetPoints := Multiset(listOfPoints);
    setPoints := Set(listOfPoints);
    
    //if any multiplicity greater then 3, use ideal method. otherwise use non-ideal method
    if &and[Multiplicity(multisetPoints, P)lt 3: P in setPoints] then 
        PointTangentPairs := [ <P, tangentLineThroughCurvePoint(f,P, Proj2Ext)>: P in setPoints |Multiplicity(multisetPoints,P) gt 1];
        cubic := curveThroughPtsWithTangent(listOfPoints, PointTangentPairs, 9, Proj2Ext);
    else 
        cubic:= groebnerMethod(listOfPoints, f, 3, Proj2Ext);
    end if;
    
    //printf "\n Cubic is %o\n",cubic;
    //cubic:= groebnerMethod(listOfPoints, f, 3, Proj2Ext);

    // Step 2. Find the divisor E*C - (DA+DB+D-Inf)

    EDOTCdata := IntersectionNumbers(Curve(Proj2Ext, cubic), Curve(Proj2Ext, f));
    //print #EDOTCdata;
    //print EDOTCdata;
    EDOTC := intersectionDataToMultiset(EDOTCdata); 
    assert Multiset(listOfPoints) subset EDOTC;
    D3 := EDOTC diff Multiset(listOfPoints);    

    /*
    print "EDOTC", #EDOTC;
    print EDOTC;
    print "D3",#D3;
    print D3;
    print "listOfPoints";
    print listOfPoints;
    */

    // Step 3. Find the quadratic through the points
    listOfPoints := [P: P in D3] cat [P1Inf, P2Inf]; 
    //print "list of points", #listOfPoints;
    assert #listOfPoints eq 5;
    multisetPoints := {*P: P in listOfPoints*};
    setPoints := Set(listOfPoints);
    
    if &and[Multiplicity(multisetPoints, P)lt 3: P in setPoints] then
        PointTangentPairs := [ <P, tangentLineThroughCurvePoint(f,P, Proj2Ext)>: P in setPoints |Multiplicity(multisetPoints,P) gt 1];
        quadric := curveThroughPtsWithTangent(listOfPoints, PointTangentPairs, 5, Proj2Ext);
    else 
        quadric := groebnerMethod(listOfPoints, f, 2, Proj2Ext);
    end if;
    
    //printf "\n quadric is %o\n",quadric;

    //quadric := groebnerMethod(listOfPoints, f, 2, Proj2Ext);

    //Step 4.  Find the left-over divisor.

    DDOTCdata := IntersectionNumbers(Curve(Proj2Ext, quadric), Curve(Proj2Ext, f));
    DDOTC := intersectionDataToMultiset(DDOTCdata);


    assert #DDOTC eq 8;
    assert Multiset(listOfPoints) subset DDOTC;
    D4Pts := [P: P in (DDOTC diff Multiset(listOfPoints))];
    
    /*
    Following is the test to a conjecture: all the points 
    at infinity that shows up in the addition process 
    are eithe P1^inf, P2^inf, or P3^inf.
    
    for pt in D4Pts do 
        if pt[3] eq 0 then 
            print "#######################";
            print pt;
            if not pt in [J`P1Inf, J`P2Inf,J`P3Inf, J`P4Inf] then 
                assert false;
            end if;
        end if;
    end for;
    */


    return <D4Pts[1],D4Pts[2],D4Pts[3]>;

end function;

/******************************************* hybrid & smart addition functions ******************************************/

/*
Solves the linear system needed for the cubic
*/
typicalAdditionHelper := function(u1,u2,v1,v2,r)
    q := #BaseRing(Parent(u1));
    X := Parent(u1).1;

    u12, u11, u10 := Explode([Coefficient(u1, power): power in [2,1,0]]);
    u22, u21, u20 := Explode([Coefficient(u2, power): power in [2,1,0]]);
    v12, v11, v10 := Explode([Coefficient(v1, power): power in [2,1,0]]);
    v22, v21, v20 := Explode([Coefficient(v2, power): power in [2,1,0]]);
    r2, r1, r0 := Explode([Coefficient(r, power): power in [2,1,0]]);

    /* These coefficients are computed by the script s-delta.m */
    M := Matrix(GF(q), 5, 5, 
    [
        -v12, 0,0,1,0,
        -v11,-v12,0,u12,1,
        1,0,0,u22*r2 - r1,-r2,
        0,1,0,u21*r2 - r0,-r1,
        0,0,1,u20*r2,-r0
    ]);

    b := Matrix(GF(q), 5, 1,
    [   
        (v12)^2,
        2*v12*v11,
        -v12 - v22,
        -v11 - v21,
        -v10 - v20
    ]);
    
    if not IsInvertible(M) then
        error Error("Atypical divisor: M is not invertible");
    end if;
    sDelCoeffs := Eltseq((M)^(-1) * b);

    s := sDelCoeffs[1]*X^2 + sDelCoeffs[2]*X + sDelCoeffs[3];
    del1 := sDelCoeffs[4]*X + sDelCoeffs[5];
    
    return s, del1;
end function;

/*
Check if the UV is valid
*/
uvIsValid := function(U,V)
    //printf "------------------------\n";
    u := UnivariatePolynomial(U);
    v := UnivariatePolynomial(V);

    uDegCorrect := Degree(u) eq 3;
    vDegCorrect := Degree(v) eq 2;
    noMult := GCD(u,Derivative(u)) eq 1;
    //printf "u=%o, Derivative=%o\n", u, Derivative(u);
    //printf "GCD(u,Derivative(u))=%o\n", GCD(u,Derivative(u));
    //printf "udeg %o,vdeg %o,nomult %o\n", uDegCorrect, vDegCorrect, noMult;

    return uDegCorrect and vDegCorrect and noMult;

end function;


/*
Implements typical addition

If the letters are lowercase, then it means 
it's a univariate polynomial.

if the letters are upper case, then it lies in $GF(q)<X,Y>$

*/
typicalAddition := function(quarticCoeffs, D1, D2)
    R := Parent(D1`u);
    U1 := D1`u; 
    V1 := D1`v;
    U2 := D2`u; 
    V2 := D2`v;
    DEHOMF := quarticCoeffs`dehomf;
    H1 := quarticCoeffs`h1;
    H2 := quarticCoeffs`h2;
    F4 := quarticCoeffs`f4;

    // Step 1. computation of the cubic E

    u1 := UnivariatePolynomial(U1);
    v1 := UnivariatePolynomial(V1);
    u2 := UnivariatePolynomial(U2);
    v2 := UnivariatePolynomial(V2);

    //assert Degree(u1) eq 3 and Degree(u2) eq 3;
    //assert Degree(v1) le 2 and Degree(v2) le 2;

    h1 := UnivariatePolynomial(H1);
    h2 := UnivariatePolynomial(H2);
    f4 := UnivariatePolynomial(F4);

    if not ((U1 eq U2) and (V1 eq V2)) then
        res, t1, _ := XGCD(v1-v2, u2);
        // If res is not 1, then we get an atypical divisor
        if not res eq 1 then 
            error Error("Atypical divisor when producing cubic");
        end if;
        r := (u1-u2)*t1 mod u2;
    else 
        omega1 := (v1^3+v1^2*h1+v1*h2 - f4) div u1;
        res, t1, _ := XGCD(omega1, u1);
        // If res is not 1, then we get an atypical divisor
        if not res eq 1 then 
            error Error("Atypical divisor when producing cubic");
        end if;
        r := (3*v1^2+2*v1*h1+h2)*t1 mod u1;
    end if;

    s, del1 := typicalAdditionHelper(u1,u2,v1,v2,r);
    
    /*
    print "Sanity check: following should be 0";
    print v1+v2+s-r*del1 mod u2;
    */

    S := Evaluate(s, R.1);
    DEL1 := Evaluate(del1, R.1);

    /*
    print "Sanity check: the degree 3, 4 coefficient should be 0";
    print -v1*(v1+s) + u1*del1;
    */
    
    Y := R.2;
    E := (Y-V1)*(Y+V1+S)+ U1*DEL1;

    // Step 2. Computation of the conic Q
    uPrime := Resultant(E, DEHOMF, Y) div (U1*U2);
    // sometimes gives this error: Runtime error: Argument 2 does not divide argument 1
    // always seem to happen when doubling
    uPrime := UnivariatePolynomial(uPrime);
    uPrime /:= LeadingCoefficient(uPrime);

    S := Coefficient(E, Y, 1);
    T := Coefficient(E, Y, 0);

    s := UnivariatePolynomial(S);
    t := UnivariatePolynomial(T);

    res, alpha1, _ := XGCD(t-s^2-h2+s*h1, uPrime);
    
    if not res eq 1 then 
        error Error("Atypical divisor when producing quartic");
    end if;

    v := alpha1*(s*t - t*h1 -f4) mod uPrime;

    // Step 3. Output the addition divisor
    u := (v^3 + v^2*h1 + v*h2 - f4) div uPrime;
    u /:= LeadingCoefficient(u);

    V := Evaluate(v, R.1);
    U := Evaluate(u, R.1);

    if not uvIsValid(U,V) then
        error "UV is invalid";
    end if;

    return <U,V>;
end function;


checkConvertibleToTypical := function(pts)
    assert #pts eq 3;

    zs := [pt[3]: pt in pts];
    allAffine := &and[not (z eq 0): z in zs];

    xs := [pt[1]: pt in pts];
    distinctX := #Set(xs) eq 3;

    if (not allAffine) or (not distinctX) then 
        return false;
    end if;

    //assert working with patch = 1
    assert &and[z eq 1: z in zs];

    x1 := pts[1][1]; y1 := pts[1][2]; 
    x2 := pts[2][1]; y2 := pts[2][2]; 
    x3 := pts[3][1]; y3 := pts[3][2]; 

    collinear := x1*(y2-y3) + x2*(y3-y1) + x3*(y1-y2) eq 0;

    if collinear then return false; end if;

    return true;

end function;