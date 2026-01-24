import "./g3utils.m": 
    intersectionDataToMultiset, 
    tangentLineThroughCurvePoint,
    createHash,
    translateStandard,
    pointBaseCoerce,
    curveThroughPtsWithTangent,
    groebnerMethod,
    generatekPoints,
    magmaSetupHelper,
    naiveAddition;

declare type G3JacNaive;
declare attributes G3JacNaive: 
    //------------------------------  following attributes are common to all three Jacobian implementations.
    Standardf, // f that defines the genus 3 curve, degree 4 homogenous polynomial in x,y,z in GF(q). This is after the transformation
    MagmaIndicator, // the constructor by default sets it to false. If it's set to true, then it uses magma's built-in function to update the lpoly/order below
    MagmaLpolyCheck, // use magma's built-in function to get its l-poly
    MagmaOrder, // use magma's built-in function to get its order
    BaseField, //GF(q)
    BaseSpace, //Projective space over (BaseField)
    ExtendedStandardf, // f base changed to GF(q^6)
    //------------------------------  following attributes are only common to G3JacNaive and G3Jac
    Identity, //G3JacNaivePoint type object with P1Inf + P2Inf + P3Inf
    ExtendedField, //GF(q^6)
    ExtendedSpace,//Projective space over (ExtendedField)
    //----------------------------- following are defined differently for different implementation of jacobians
    LInf, // line that intersects f at 4 rational points, with intersection pts (2,1,1). default z=0
    P1Inf, // (0:1:0) point on LInf
    P2Inf, // (0:1:0) point on LInf
    P3Inf, // (x:y:0) point on LInf
    P4Inf; // (1:0:0) point on Linf

declare type G3JacNaivePoint;
declare attributes G3JacNaivePoint: 
    Parent, //type G3JacNaive object
    D, //multiset consisted of the three points
    hash; //divisor of the form {*P1,P2,P3*}

/*
G3JacNaivePoint constructor
*/
intrinsic G3JacNaivePointCreation(J::G3JacNaive, P1::Pt, P2::Pt, P3::Pt) -> G3JacNaivePoint
{Takes Jacobian J and three points}
    JP := New(G3JacNaivePoint);
    JP`Parent := J;
    assert &and[Evaluate(J`ExtendedStandardf, [P[1],P[2],P[3]]) eq 0: P in [P1,P2,P3]];
    JP`D := {*P1,P2,P3*};
    JP`hash := createHash(JP`D,J);
    return JP;
end intrinsic;

/*
Constructor for G3JacNaive object

If setupMagma flag is set to true, then it uses magma to compute l-poly.
Then it translates f so that its rational intersection number with line l=z is (2,1,1)
Lastly, it sets its identity.
*/

intrinsic G3JacNaiveCreation(definingEquation::RngMPolElt : setupMagma:=false) -> G3JacNaive
{Takes a polynomial of defined in GF(q)[x,y,z] or GF(q^2)[x,y,z] and make it 
into type G3JacNaive}

    //Setup basic attributes code
    J := New(G3JacNaive);
    q := #BaseRing(Parent(definingEquation));
    J`BaseField := GF(q);
    Proj2<x,y,z> := ProjectiveSpace(GF(q),2);
    J`BaseSpace := Proj2;

    //Translate so that it's in the standard form
    J`Standardf, J`LInf, P1234 := translateStandard(definingEquation, Proj2, J`BaseField);

    //Setup magma helper
    J`MagmaIndicator := setupMagma; 

    if setupMagma then 
        magmaLpoly := magmaSetupHelper(J`BaseSpace, definingEquation);
        J`MagmaLpolyCheck := magmaLpoly;
        J`MagmaOrder := Evaluate(J`MagmaLpolyCheck,1);
    end if;

    // Setup extended field

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
    J`Identity := G3JacNaivePointCreation(J, J`P1Inf, J`P2Inf, J`P3Inf);
    //Sanity check
    //assert (J`Identity + J`Identity)`D eq (J`Identity)`D;
    return J;
end intrinsic;


intrinsic Print(J::G3JacNaive){}
	printf "Jacobian whose standard curve defined by %o\n", J`Standardf;
    printf "of order %o, of l-poly %o\n", J`MagmaOrder, J`MagmaLpolyCheck;
    printf "in base field %o\n", J`BaseField;
    printf "with intersecting line %o\n", J`LInf;
    printf "with P1 = %o, P2 = %o, P3 = %o, P4 = %o\n", J`P1Inf, J`P2Inf, J`P3Inf, J`P4Inf;
    printf "in base projective space %o and \n extended projective space %o\n", J`BaseSpace, J`ExtendedSpace;
end intrinsic;


intrinsic Print(P::G3JacNaivePoint){}
	printf "\n Point defined by %o ", P`D;
	printf "\n on the jacobian of %o ", (P`Parent)`Standardf;
    printf "\n with hash %o\n\n", P`hash;
end intrinsic;


intrinsic generateGeneralPoint(J::G3JacNaive)->G3JacNaivePoint
{Generate random point of the form P1,P2,P3 }
    pts := generatekPoints(J, 3);
    return G3JacNaivePointCreation(J, pts[1], pts[2], pts[3]);
end intrinsic;


intrinsic generateDoublePoint(J::G3JacNaive)->G3JacNaivePoint
{Generate random point of the form P1,P1,P2}
    pts := generatekPoints(J, 2);
    return G3JacNaivePointCreation(J, pts[1], pts[1], pts[2]);
end intrinsic;


intrinsic generateTriplePoint(J::G3JacNaive)->G3JacNaivePoint
{Generate random point of the form P1,P1,P1}
    pts := generatekPoints(J, 1);
    return G3JacNaivePointCreation(J, pts[1], pts[1], pts[1]);
end intrinsic;

/*
Implements the group addition. See paper for details
*/
intrinsic '+'(DA::G3JacNaivePoint, DB::G3JacNaivePoint)->G3JacNaivePoint 
{naive addition in extended field (not using galois orbits) }
    J := DA`Parent;
    f := J`ExtendedStandardf;
    Proj2Ext := J`ExtendedSpace;

    D4Pts := naiveAddition(f, Proj2Ext, DA`D, DB`D, J`P1Inf, J`P2Inf, J`P3Inf, J`P4Inf);
    D4 := G3JacNaivePointCreation(J, D4Pts[1],D4Pts[2],D4Pts[3]);

    return D4;

end intrinsic;

/*
Computes the negation of a point. See paper for details.
*/
intrinsic '-'(D1::G3JacNaivePoint)-> G3JacNaivePoint
{compute the negation of a point}
    J := D1`Parent;
    f := J`ExtendedStandardf;
    Proj2Ext := J`ExtendedSpace;
    D1, D2, D3 := Explode([P: P in D1`D]);

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

    DInv := G3JacNaivePointCreation(J, D4Pts[1],D4Pts[2],D4Pts[3]);
    return DInv;
end intrinsic;

intrinsic '-'(D1::G3JacNaivePoint, D2::G3JacNaivePoint)-> G3JacNaivePoint
{compute the negation of a point}
    return D1 + (-D2);
end intrinsic;

intrinsic '*'(n::RngIntElt, D::G3JacNaivePoint)->G3JacNaivePoint 
{double and add using naive addition}
    assert n ge 0;
    if n eq 0 then
        return (D`Parent)`Identity;
    end if;
    Acc := D;
    binString := Reverse(Intseq(n,2));
    divisorsAlongWay := [];
    for idx in [2..#binString] do    
        d := binString[idx];
        //print "iteration number";
        //print idx;
        Acc := Acc + Acc;
        if d eq 1 then 
            Acc := Acc + D;
        end if;

        Append(~divisorsAlongWay, Acc);
    end for;

    //print "divisorsAlongWay",divisorsAlongWay;
    return Acc;

end intrinsic;

intrinsic checkIsId(D1::G3JacNaivePoint)->BoolElt
{check if a point is identity}
    return D1`D eq ((D1`Parent)`Identity)`D;
end intrinsic;

