# lift_g3_public
Lifting L polynomials of genus 3 curves

This repository provides a Magma program for "lifting $L$-polynomial of genus 3 curves", see [https://arxiv.org/abs/2602.00965](https://arxiv.org/abs/2602.00965).

## Demo 1

**Usage:**
Run the following in a Magma shell from the top-level directory:

 ```load "liftDemo.m";``` 

- We have 5 curves 
- Each curve is tested against four primes $p$ of bitlengths 10, 15, 20, 25.
- Input: $[a_1 \bmod p, a_2 \bmod p, a_3 \bmod p]$ 
- Output: $[a_1, a_2, a_3]$ and timings

## Demo 2

**Usage:**
Run the following in a Magma shell from the top-level directory:

 ```load "groupDemo.m";``` 
- We have 3 curves, for each curve, we have two primes, $p_1, p_2$, of bitlength $10, 25$ respectively.
- Then, for $q\in [p_1,p_1^2, p_2, p_2^2]$, we generate a random element $D$ in $J(C)(\mathbb{F}_q)$ and 
multiply $D$ by the size of $J(C)(\mathbb{F}_q)$.
- We verify that it equals identity.
- We compare the timings between naive addition and hybrid addition



## Algorithms in the paper 

Inside ```src/g3/g3utils.m```:
- Algorithm 1 (Naive point addition) corresponds to ```naiveAddition := function(f, Proj2Ext, DAset, DBset, P1Inf, P2Inf, P3Inf, P4Inf)```
- Algorithm 2 (Linear algebra interpolation) and Algorithm 3 (Ideal interpolation) are part of Algorithm 1.
- Typical addition algorithm in [https://eprint.iacr.org/2004/118](https://eprint.iacr.org/2004/118) corresponds to ```typicalAddition := function(quarticCoeffs, D1, D2)```

Inside ```src/g3/g3Naive.m```:
- Algorithm 4 (divisor inversion) corresponds to ```intrinsic '-'(D1::G3JacNaivePoint)-> G3JacNaivePoint```

Inside ```src/g3/g3Hybrid.m```:
- Algorithm 5 (Hybrid addition algorithm) corresponds to ```intrinsic '+'(D1::G3JacHybridPoint, D2::G3JacHybridPoint)->G3JacHybridPoint```

Inside ```src/general/lpolyBSGS.m```:
- Algorithm 6 (Step 2. Baby-step giant-step algorithm) corresponds to ```lPolyWrapper := function(fOverQ, f, p, lpolymodResults : method := "hybrid", a2Indicator := false, a2Value := 0)```


