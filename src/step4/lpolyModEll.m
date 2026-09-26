/*
Step 4 of the genus-3 L-polynomial lifting algorithm: L_p(T) mod ell for a
small prime ell != p (Algorithm Compute-L-poly-mod-ell of the paper).

  safeExtensionDegree       Definition of the safe extension degree K
  attemptToBuildEllTorsion  Attempt-to-build-ell-torsion
  lPolyModEllHelper         Compute-L-poly-mod-ell-helper
  computeLPolyModEll        Compute-L-poly-mod-ell

Group arithmetic is the G3JacHybrid Jacobian (g3Hybrid.spec); the abelian
p-group algorithms of [Sut10] come from pGroup.m.  Candidates are integer
polynomials L_i(T) = L_{p,a_1,a_2,a_3}(T); the curve C is given by its plane
quartic over GF(p).
*/


// X^6 L(1/X) over the ring R, for L of degree 6 with nonzero constant term.
// Converts between L(T) = det(1 - FT) and chi_F(X) = det(X - F) in either direction.
reciprocal := function(L, R)
    assert Degree(L) eq 6;
    return R ! Reverse(Coefficients(L));
end function;


// Predicted #Jac(C)(F_(p^k)) = |Res(T^k - 1, L(T))| for each candidate L.
predictedOrders := function(Ls, k)
    T := Universe(Ls).1;
    return [ Abs(Resultant(T^k - 1, L)) : L in Ls ];
end function;


intrinsic safeExtensionDegree(L::RngUPolElt, ell::RngIntElt) -> RngIntElt
{The safe extension degree K = ell^r * prod_j (ell^(d_j) - 1) of the candidate
 L(T) at the prime ell, where chi = X^6 L(1/X) mod ell = prod_j f_j^(e_j) with
 deg f_j = d_j and r = ceil(log_ell max_j e_j).  If L is the true L-polynomial
 then Jac(C)[ell] is rational over F_(p^K).}
    chi := reciprocal(L, PolynomialRing(GF(ell)));
    factors := Factorization(chi);
    maxMultiplicity := Max([ fe[2] : fe in factors ]);
    r := 0;
    while ell^r lt maxMultiplicity do r +:= 1; end while;
    return ell^r * &*[ ell^Degree(fe[1]) - 1 : fe in factors ];
end intrinsic;


intrinsic attemptToBuildEllTorsion(k::RngIntElt, ell::RngIntElt, f::RngMPolElt, Ls::SeqEnum
    : numSamples := 8) -> BoolElt, Assoc, SeqEnum
{Attempt-to-build-ell-torsion.  Draws numSamples random points of the ell-Sylow
 subgroup of Jac(C)(F_(p^k)) (cofactor = lcm of the candidates' predicted orders
 with the ell-part removed) and runs Algorithm 4 of [Sut10] on them, stopping as
 soon as its basis has six elements.  On success returns true, the table
 hash-to-vec mapping each of the ell^6 points of Jac(C)[ell] to its coordinate
 vector, and the basis e_1, ..., e_6 of Jac(C)[ell]; otherwise returns false.
 Requires the true L-polynomial to be among Ls.}
    p := Characteristic(BaseRing(Parent(f)));
    J := G3JacHybridCreation(ChangeRing(f, GF(p^k)));
    zero := Zero(J);

    N := LCM(predictedOrders(Ls, k));
    cap := Valuation(N, ell);                        // ell-Sylow exponent is at most ell^cap
    cofactor := N div ell^cap;
    S := [ cofactor * Random(J) : i in [1..numSamples] ];
    error if not forall{ s : s in S | ell^cap * s eq zero },
        "a sample is not in the ell-Sylow subgroup: no candidate is the true L-polynomial";

    basis, nvec := pGroupBasis(S, ell, cap : maxRank := 6);
    if #basis lt 6 then
        return false, _, _;
    end if;
    // Independent multiples of order ell form a basis of Jac(C)[ell] = (Z/ell)^6.
    basis := [ ell^(nvec[i] - 1) * basis[i] : i in [1..6] ];

    // hash-to-vec: enumerate the ell^6 F_ell-combinations of the basis.
    V := VectorSpace(GF(ell), 6);
    points := [zero];
    vectors := [V ! 0];
    for i in [1..6] do
        n := #points;
        step := zero;
        for c in [1..ell-1] do
            step := step + basis[i];                 // step = c * basis[i]
            for j in [1..n] do
                Append(~points, points[j] + step);
                Append(~vectors, vectors[j] + c * V.i);
            end for;
        end for;
    end for;
    hashToVec := AssociativeArray();
    for j in [1..#points] do
        hashToVec[points[j]`hash] := vectors[j];
    end for;
    assert #Keys(hashToVec) eq ell^6;               // the ell^6 points are distinct
    return true, hashToVec, basis;
end intrinsic;


intrinsic lPolyModEllHelper(basis::SeqEnum, hashToVec::Assoc) -> RngUPolElt
{Compute-L-poly-mod-ell-helper.  Given a basis e_1, ..., e_6 of Jac(C)[ell] and
 the table hash-to-vec from attemptToBuildEllTorsion, reads off the matrix of
 Frobenius on Jac(C)[ell] and returns L_p(T) mod ell, the reciprocal of its
 characteristic polynomial.}
    rows := [];
    for e in basis do
        found, v := IsDefined(hashToVec, Frobenius(e)`hash);
        error if not found, "Frobenius image is not in the ell-torsion table";
        Append(~rows, v);
    end for;
    // Row i is F(e_i); the transpose has the same characteristic polynomial.
    chi := CharacteristicPolynomial(Matrix(rows));
    return reciprocal(chi, Parent(chi));
end intrinsic;


intrinsic computeLPolyModEll(Ls::SeqEnum, f::RngMPolElt, ell::RngIntElt
    : attemptsPerDegree := 2, maxPasses := 4, verbose := false) -> RngUPolElt
{Compute-L-poly-mod-ell.  Given the candidate L-polynomials Ls (integer
 polynomials in T, one of which is the true L_p(T)), the plane quartic f of C
 over GF(p), and a prime ell != p, returns L_p(T) mod ell over GF(ell).  The
 trial extension degrees are the divisors of the candidates' safe extension
 degrees.  Each degree is attempted up to attemptsPerDegree times before moving
 on (an unlucky sample set is much cheaper to redraw than the next degree), and
 the whole list is retried with fresh randomness up to maxPasses times.}
    Ks := [ safeExtensionDegree(L, ell) : L in Ls ];
    degreeTries := Sort(Setseq(&join[ Set(Divisors(K)) : K in Ks ]));
    if verbose then
        printf "  [ell=%o] K_i = %o, Degree-tries = %o\n", ell, Ks, degreeTries;
    end if;
    for pass in [1..maxPasses] do
        for k in degreeTries do
            // Jac(C)(F_(p^k)) contains Jac(C)[ell] only if ell^6 divides its order.
            if forall{ N : N in predictedOrders(Ls, k) | Valuation(N, ell) lt 6 } then
                continue;
            end if;
            for attempt in [1..attemptsPerDegree] do
                success, hashToVec, basis := attemptToBuildEllTorsion(k, ell, f, Ls);
                if verbose then
                    printf "  [ell=%o] k = %o, attempt %o: %o\n",
                        ell, k, attempt, success select "success" else "failed";
                end if;
                if success then
                    return lPolyModEllHelper(basis, hashToVec);
                end if;
            end for;
        end for;
    end for;
    error Sprintf("computeLPolyModEll: no trial degree succeeded in %o passes", maxPasses);
end intrinsic;
