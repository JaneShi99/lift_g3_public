/*
Algorithm 8 from the genus-3 paper: the Sylow-subgroup eliminator.

Depends on the p-group library primitives in pGroup.m (in particular
sylowVerifier). This file is meant to be attached together with pGroup.m
via sylowEliminator.spec, not on its own.
*/

freeze;


// ---- chooseDistinguishingPrime ----

intrinsic chooseDistinguishingPrime(Li::RngIntElt, Lj::RngIntElt) -> RngIntElt, RngIntElt
{Given L_i != L_j, returns (ell, b) where ell^(b+1) divides L_i and ell^b exactly divides L_j.
 Picks any prime factor of L_i / gcd(L_i, L_j).}
    assert Li ne Lj;
    d := Li div GCD(Li, Lj);
    assert d gt 1;
    // Factor d, pick the first prime factor
    fac := Factorization(d);
    ell := fac[1][1];
    b := Valuation(Lj, ell);
    return ell, b;
end intrinsic;


// ---- Sylow-subgroup eliminator (Algorithm 8) ----

intrinsic sylowEliminator(
    candidateOrders::SeqEnum,
    G::.,
    maxRank::RngIntElt
    : verbose := false
) -> RngIntElt
{Algorithm 8 from the genus-3 paper. Given candidate group orders and a group G,
 eliminates wrong candidates via Sylow-subgroup arguments.
 Returns the unique surviving candidate order.
 Optional parameter verbose (default false): prints a trace of each pair
 comparison and elimination.}
    k := #candidateOrders;
    assert k ge 1;
    if k eq 1 then
        return candidateOrders[1];
    end if;

    eliminated := {};
    max_rounds := 100;
    num_samples := maxRank + 2;

    if verbose then
        printf "[elim] starting with %o candidates, num_samples = %o\n", k, num_samples;
    end if;

    for round in [1..max_rounds] do
        if k - #eliminated eq 1 then
            survivor := [c : c in [1..k] | c notin eliminated][1];
            if verbose then printf "[elim] converged: survivor is candidate %o = %o\n", survivor, candidateOrders[survivor]; end if;
            return candidateOrders[survivor];
        end if;

        if verbose then
            printf "[elim] ---- round %o ----  alive: %o\n",
                round, [c : c in [1..k] | c notin eliminated];
        end if;

        for i in [1..k] do
            if i in eliminated then continue; end if;
            for j in [1..k] do
                if j in eliminated or j eq i then continue; end if;

                Li := candidateOrders[i];
                Lj := candidateOrders[j];

                // Skip if L_i divides L_j (no prime where L_i has higher valuation)
                d := Li div GCD(Li, Lj);
                if d eq 1 then
                    if verbose then
                        printf "  (i=%o L_i=%o) vs (j=%o L_j=%o): L_i | L_j, skip\n",
                            i, Li, j, Lj;
                    end if;
                    continue;
                end if;

                // Choose distinguishing prime
                ell, b := chooseDistinguishingPrime(Li, Lj);
                target_exp := b + 1;

                // Produce ell-Sylow elements assuming L_i is correct
                ell_val_Li := Valuation(Li, ell);
                cofactor := Li div ell^ell_val_Li;
                sylow_elts := [cofactor * Random(G) : s in [1..num_samples]];

                verified := sylowVerifier(sylow_elts, ell, target_exp);

                if verbose then
                    printf "  (i=%o L_i=%o) vs (j=%o L_j=%o): ell=%o, v_ell(L_i)=%o, v_ell(L_j)=%o, target=ell^%o; verifier=%o",
                        i, Li, j, Lj, ell, ell_val_Li, b, target_exp, verified;
                end if;

                if verified then
                    // Eliminate all candidates not divisible by ell^target_exp
                    killed := [];
                    for c in [1..k] do
                        if c notin eliminated and Valuation(candidateOrders[c], ell) lt target_exp then
                            Include(~eliminated, c);
                            Append(~killed, c);
                        end if;
                    end for;
                    if verbose then
                        if #killed eq 0 then
                            printf " -> eliminated nothing new\n";
                        else
                            printf " -> eliminated %o\n", killed;
                        end if;
                    end if;
                else
                    if verbose then printf " -> no elimination\n"; end if;
                end if;

                if k - #eliminated eq 1 then
                    survivor := [c : c in [1..k] | c notin eliminated][1];
                    if verbose then
                        printf "[elim] converged: survivor is candidate %o = %o\n",
                            survivor, candidateOrders[survivor];
                    end if;
                    return candidateOrders[survivor];
                end if;
            end for;
        end for;
    end for;

    error "sylowEliminator did not converge after", max_rounds, "rounds";
end intrinsic;
