/*
Sutherland's algorithms for abelian p-groups [Sut10].
  1. Order computation
  2. Base-case DLP (brute-force enumeration in elementary abelian groups)
  3. Algorithm 3 (DL* — recursive discrete log)
  4. Algorithm 4 (basis construction from a generating set)
*/

freeze;


// ---- Section 2: Order computation ----

intrinsic pGroupOrder(alpha::., p::RngIntElt, cap::RngIntElt) -> RngIntElt
{Given alpha in an abelian p-group, returns h such that |alpha| = p^h.
 If h > cap, returns cap+1 as an "exceeded" sentinel.
 Assumes alpha has order a power of p.}
    zero := Zero(Parent(alpha));
    if alpha eq zero then
        return 0;
    end if;
    current := alpha;
    for h in [1..cap] do
        current := p * current;
        if current eq zero then
            return h;
        end if;
    end for;
    return cap + 1;
end intrinsic;


// ---- Section 3: Base-case DLP in elementary abelian (Z/pZ)^r ----

intrinsic elementaryAbelianDL(
    basis::SeqEnum,
    target::.,
    p::RngIntElt
) -> SeqEnum
{Returns [e_1, ..., e_r] in [0,p)^r with target = sum e_i * basis[i],
 or empty sequence if target is not in <basis>.
 Brute-force enumeration — O(p^r) group ops.}
    r := #basis;
    zero := Zero(Parent(target));

    // Enumerate all tuples (e_1, ..., e_r) in [0, p)^r
    for e in [0..p^r - 1] do
        // Extract base-p digits, least significant first, padded to length r
        digits := [];
        tmp := e;
        for i in [1..r] do
            Append(~digits, tmp mod p);
            tmp := tmp div p;
        end for;

        candidate := zero;
        for i in [1..r] do
            if digits[i] ne 0 then
                candidate := candidate + digits[i] * basis[i];
            end if;
        end for;

        if candidate eq target then
            return digits;
        end if;
    end for;

    return [];
end intrinsic;


// ---- Section 4: Algorithm 3 helpers ----

// q_i(j, k) = p^{j + max(0, n_i - k)}
// Returns the vector [q_1, ..., q_r].
intrinsic q_vector(n_vec::SeqEnum, j::RngIntElt, k::RngIntElt, p::RngIntElt) -> SeqEnum
{Compute the q-vector for the subgroup G(j,k).}
    return [p^(j + Max(0, n_i - k)) : n_i in n_vec];
end intrinsic;

// alpha(j, k) = [alpha_i^{q_i(j,k)} : i in [1..r]]
// These are the basis elements for the subgroup G(j, k).
intrinsic alpha_jk(alpha_basis::SeqEnum, n_vec::SeqEnum, j::RngIntElt, k::RngIntElt, p::RngIntElt) -> SeqEnum
{Compute the basis for the subgroup G(j,k).}
    qs := q_vector(n_vec, j, k, p);
    return [qs[i] * alpha_basis[i] : i in [1..#alpha_basis]];
end intrinsic;

// Componentwise quotient: q(j_num, k_num) / q(j_den, k_den), as scalars.
// Valid when j_num >= j_den and k_num <= k_den.
intrinsic q_div(n_vec::SeqEnum, j_num::RngIntElt, k_num::RngIntElt, j_den::RngIntElt, k_den::RngIntElt, p::RngIntElt) -> SeqEnum
{Componentwise quotient of q-vectors.}
    assert j_num ge j_den and k_num le k_den;
    result := [];
    for n_i in n_vec do
        num_exp := j_num + Max(0, n_i - k_num);
        den_exp := j_den + Max(0, n_i - k_den);
        Append(~result, p^(num_exp - den_exp));
    end for;
    return result;
end intrinsic;

// Partition the column strip (j, k] into w sub-strips.
// Returns [j_1, j_2, ..., j_{w+1}] with j_1 = j, j_{w+1} = k.
// Widths are as equal as possible.
intrinsic partitionColumns(j::RngIntElt, k::RngIntElt, w::RngIntElt) -> SeqEnum
{Partition a column strip into w sub-strips of near-equal width.}
    assert w ge 1 and w le k - j;
    total := k - j;
    q := total div w;
    rho := total mod w;

    points := [j];
    current := j;
    for i in [1..w] do
        width := (i le rho) select q + 1 else q;
        current := current + width;
        Append(~points, current);
    end for;
    assert current eq k;
    return points;
end intrinsic;


// Base case for DL* on a width-1 strip (j, j+1].
// Returns <x, h> where x is the DL vector and h is the witness exponent.
// h = 0 means beta is in G(j, j+1); h = 1 means it is not.
intrinsic baseCaseDLStar(
    alpha_basis::SeqEnum,
    n_vec::SeqEnum,
    p::RngIntElt,
    j::RngIntElt,
    k::RngIntElt,
    beta::.
) -> Tup
{Base case for DL*: solve DLP in the elementary abelian layer G(j, k).
 Assumes k - j = 1.}
    assert k - j eq 1;
    r := #alpha_basis;

    // Construct basis for G(j, j+1)
    base := alpha_jk(alpha_basis, n_vec, j, k, p);

    // Only indices where n_i > j contribute non-trivially
    activeIndices := [l : l in [1..r] | n_vec[l] gt j];
    activeBase := [base[l] : l in activeIndices];

    result := elementaryAbelianDL(activeBase, beta, p);

    if #result eq 0 then
        // beta not in the subgroup — return failure witness
        return <[0 : i in [1..r]], 1>;
    end if;

    // Zero-pad result back to full r-vector
    full_x := [0 : i in [1..r]];
    for idx in [1..#activeIndices] do
        full_x[activeIndices[idx]] := result[idx];
    end for;
    return <full_x, 0>;
end intrinsic;


// ---- Section 4: Algorithm 3 (DL*) ----

intrinsic pGroupDLStar(
    alpha_basis::SeqEnum,
    n_vec::SeqEnum,
    p::RngIntElt,
    j::RngIntElt,
    k::RngIntElt,
    beta::.
) -> Tup
{Algorithm 3 from [Sut10]. Recursive discrete log in an abelian p-group.
 Returns <x, h> where x is a DL vector and h is a witness exponent.
 h = 0 means beta is in <alpha_basis>; h > 0 means it is not.
 Uses base-case threshold t = 1 throughout.}
    r := #alpha_basis;
    zero := Zero(Parent(beta));

    // Base case: strip has width <= 1 (t = 1 hardcoded; revisit for t > 1 later)
    if k - j le 1 then
        return baseCaseDLStar(alpha_basis, n_vec, p, j, k, beta);
    end if;

    // Choose w = 2 (binary split) for simplicity.
    // Paper's formula: w = Min(k - j, Ceiling(Log(2, 2 * (k - j))))
    w := Min(k - j, 2);
    partition := partitionColumns(j, k, w);

    // Step 3: compute gamma_i = p^{j_i - j} * beta for i in [1..w]
    gammas := [];
    current := beta;
    Append(~gammas, current);
    for i in [2..w] do
        shift := partition[i] - partition[i-1];
        for s in [1..shift] do
            current := p * current;
        end for;
        Append(~gammas, current);
    end for;

    // Step 4: process sub-strips from rightmost (w) down to leftmost (1)
    x := [0 : i in [1..r]];

    for i in [w..1 by -1] do
        j_i := partition[i];
        j_ip1 := partition[i+1];

        // Compute gamma_i - alpha(j_i, k)^x  (adjustment for already-found coords)
        a_jk := alpha_jk(alpha_basis, n_vec, j_i, k, p);
        adjustment := zero;
        for l in [1..r] do
            if x[l] ne 0 then
                adjustment := adjustment + x[l] * a_jk[l];
            end if;
        end for;
        input_to_recurse := gammas[i] - adjustment;

        // Recursive call
        result := pGroupDLStar(alpha_basis, n_vec, p, j_i, j_ip1, input_to_recurse);
        v := result[1];
        h := result[2];

        // Compute s = q(j_i + h, j_{i+1}) / q(j_i + h, k)
        s_vec := q_div(n_vec, j_i + h, j_ip1, j_i + h, k, p);

        // x <- s * v + x, componentwise
        for l in [1..r] do
            x[l] := x[l] + s_vec[l] * v[l];
        end for;

        // Early termination if h > 0.  The recursive h is relative to j_i;
        // the result must be relative to j (Algorithm 3 returns j_i + h,
        // which assumes j = 0).
        if h gt 0 then
            return <x, j_i - j + h>;
        end if;
    end for;

    return <x, 0>;
end intrinsic;


// ---- Section 5: Algorithm 4 (basis construction) ----

intrinsic pGroupBasis(
    S::SeqEnum,
    p::RngIntElt,
    maxOrderExp::RngIntElt
    : maxRank := Infinity()
) -> SeqEnum, SeqEnum
{Algorithm 4 from [Sut10]. Given a generating set S for an abelian p-group,
 returns basis, n_vec where basis is the constructed basis and
 n_vec[i] = v_p(|basis[i]|).
 Optional parameter maxRank (default unbounded): stop as soon as the basis
 has maxRank elements, without reducing the remaining elements of S.}
    zero := Zero(Parent(S[1]));

    // Step 1: compute orders of all elements in S
    h := [pGroupOrder(s, p, maxOrderExp) : s in S];
    beta := [s : s in S];

    alpha_basis := [];
    n_vec := [];

    while true do
        // Step 2: terminate if all h[i] = 0
        if forall{i : i in [1..#h] | h[i] eq 0} then
            return alpha_basis, n_vec;
        end if;

        // Pick the element with largest h, append to basis
        max_h := Max(h);
        max_idx := [i : i in [1..#h] | h[i] eq max_h][1];
        Append(~alpha_basis, beta[max_idx]);
        Append(~n_vec, h[max_idx]);
        beta[max_idx] := zero;
        h[max_idx] := 0;

        // Early exit once the requested rank is reached
        if #alpha_basis ge maxRank then
            return alpha_basis, n_vec;
        end if;

        // Step 3: reduce all remaining beta[i] against current basis
        m := n_vec[1];  // max of n_vec, since we pick largest first
        for i in [1..#beta] do
            if h[i] gt 0 then
                result := pGroupDLStar(alpha_basis, n_vec, p, 0, m, beta[i]);
                x := result[1];
                h_new := result[2];

                // beta[i] <- beta[i] - alpha^x
                reducer := zero;
                for l in [1..#alpha_basis] do
                    if x[l] ne 0 then
                        reducer := reducer + x[l] * alpha_basis[l];
                    end if;
                end for;
                beta[i] := beta[i] - reducer;
                h[i] := h_new;
            end if;
        end for;
    end while;
end intrinsic;


// ---- Section 6: Sylow verifier (modified Algorithm 4) ----

intrinsic sylowVerifier(
    S::SeqEnum,
    p::RngIntElt,
    n::RngIntElt
) -> BoolElt
{Modified Algorithm 4: returns true if elements of S generate a subgroup
 of order >= p^n. Returns false if target not reached (probabilistic).
 true is a proof; false is not.}
    zero := Zero(Parent(S[1]));

    // Compute orders, capping at n (no need to go higher)
    h := [pGroupOrder(s, p, n) : s in S];
    beta := [s : s in S];

    alpha_basis := [];
    n_vec := [];

    while true do
        // If any single element has order >= p^n, done
        if exists{i : i in [1..#h] | h[i] ge n} then
            return true;
        end if;

        // Terminate if all h[i] = 0
        if forall{i : i in [1..#h] | h[i] eq 0} then
            return #n_vec gt 0 and &+n_vec ge n;
        end if;

        // Pick largest h[i], append to basis
        max_h := Max(h);
        max_idx := [i : i in [1..#h] | h[i] eq max_h][1];
        Append(~alpha_basis, beta[max_idx]);
        Append(~n_vec, h[max_idx]);
        beta[max_idx] := zero;
        h[max_idx] := 0;

        // Early exit: basis order already reaches target
        if &+n_vec ge n then
            return true;
        end if;

        // Reduce remaining elements against current basis
        m := n_vec[1];
        for i in [1..#beta] do
            if h[i] gt 0 then
                result := pGroupDLStar(alpha_basis, n_vec, p, 0, m, beta[i]);
                x := result[1];
                h_new := result[2];

                reducer := zero;
                for l in [1..#alpha_basis] do
                    if x[l] ne 0 then
                        reducer := reducer + x[l] * alpha_basis[l];
                    end if;
                end for;
                beta[i] := beta[i] - reducer;
                h[i] := h_new;
            end if;
        end for;
    end while;
end intrinsic;
