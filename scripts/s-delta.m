q := 1259;
F := GF(q);

// Following is the code for 
// getting the linear system for addition, but not doubling

P<x, 
    u12, u11, u10, 
    v12, v11, v10, 
    u22, u21, u20,
    v22, v21, v20, 
    r2, r1, r0, 
    s2, s1, s0,
    del11, del10 >:= PolynomialRing(Rations(), 21);


u1 := x^3 + u12*x^2 + u11*x + u10;
v1 := v12*x^2 + v11*x + v10;

u2 := x^3 + u22*x^2 + u21*x + u20;
v2 := v22*x^2 + v21*x + v20;

r := r2*x^2 + r1*x + r0;
s := s2*x^2 + s1*x + s0;
del1 := del11*x + del10;

eq1 := -v1*(v1+s) + u1*del1;
print "eq1:\n", eq1;
eq2 := v1 + v2 + s - r*del1 + r2*del11*u2;
print "eq2:\n", eq2;

assert Coefficient(eq2, x, 3) eq 0;

unknowns := [s2,s1,s0,del11,del10];

conds := [];

Append(~conds, Coefficient(eq1, x, 4));
Append(~conds, Coefficient(eq1, x, 3));
Append(~conds, Coefficient(eq2, x, 2));
Append(~conds, Coefficient(eq2, x, 1));
Append(~conds, Coefficient(eq2, x, 0));
print "all the linear conditions;";
print conds;

system := [];
b := [];

for cond in conds do
    linearCoefficients := [Coefficient(cond, unknown, 1): unknown in unknowns];
    Append(~system, linearCoefficients);
    constantCoefficient := cond - &+[linearCoefficients[i] * unknowns[i]: i in [1..#unknowns]];
    //Note: the negative sign here is crucial because we move the constant 
    //to the other side of the equation
    Append(~b, -constantCoefficient);
end for;

print system;
print b;