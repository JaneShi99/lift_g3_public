# lift_g3_public
Lifting L polynomials of genus 3 curves

This repository provides a Magma program for "lifting $L$-polynomial of genus 3 curves", see [https://arxiv.org/abs/2602.00965](https://arxiv.org/abs/2602.00965).

Given $[a_1 \bmod p, a_2 \bmod p, a_3 \bmod p]$, the algorithm determines $L_p(T)$ in four steps: Step 1 bounds the candidates, Step 2 eliminates them by baby-step giant-step, and in the rare cases where several remain, Step 3 (Sylow-subgroup eliminator) and Step 4 ($L_p(T) \bmod 2, 3$) single out the correct one.

Run all demos in a Magma shell from the top-level directory. Their inputs are hardcoded.

``magma -b groupDemo.m``
``magma -b Step2Demo.m``
``magma -b Step3Demo.m``
``magma -b Step4Demo.m``


## Group operation demo

``magma -b groupDemo.m``

- We have 3 curves, for each curve, we have two primes, $p_1, p_2$, of bitlength $10, 25$ respectively.
- Then, for $q\in [p_1,p_1^2, p_2, p_2^2]$, we generate a random element $D$ in $J(C)(\mathbb{F}_q)$ and 
multiply $D$ by the size of $J(C)(\mathbb{F}_q)$.
- We verify that it equals identity.
- We compare the timings between naive addition and hybrid addition

## Step 2 demo

``magma -b Step2Demo.m``

- We have 5 curves 
- Each curve is tested against four primes $p$ of bitlengths 10, 15, 20, 25.
- Input: $[a_1 \bmod p, a_2 \bmod p, a_3 \bmod p]$ 
- Output: $[a_1, a_2, a_3]$ and timings


## Step 3 demo

 ```load "Step3Demo.m";``` 
- We have 15 curve/prime pairs, $p\in[1601, 2027]$, from Subsection 7.4, where Step 2 leaves 2 to 6 candidates.
- Input: the candidate triples $[a_1, a_2, a_3]$ surviving Step 2
- Output: the candidate surviving the Sylow-subgroup eliminator, checked against the true $L$-polynomial, and timings

## Step 4 demo

 ```load "Step4Demo.m";``` 
- Same 15 instances and inputs as the Step 3 demo.
- We compute $L_p(T) \bmod 2$, discard the candidates that disagree, then repeat with $L_p(T) \bmod 3$.
- Output: $L_p(T) \bmod \ell$, the surviving candidates, and timings (a few minutes in total)

## Algorithms in the paper 

Inside ```src/g3/g3utils.m```:
- Algorithm 1 (Naive point addition) corresponds to ```naiveAddition```
- Algorithm 2 (Linear algebra interpolation) and Algorithm 3 (Ideal interpolation) correspond to ```curveThroughPtsWithTangent``` and ```groebnerMethod```
- Typical addition algorithm in [https://eprint.iacr.org/2004/118](https://eprint.iacr.org/2004/118) corresponds to ```typicalAddition```

Inside ```src/g3/g3Naive.m``` and ```src/g3/g3Hybrid.m```:
- Algorithm 4 (Divisor inversion) corresponds to ```intrinsic '-'(D1::G3JacNaivePoint)``` and ```intrinsic '-'(D1::G3JacHybridPoint)```, via ```negationPts``` in ```g3utils.m```
- Algorithm 5 (Hybrid addition algorithm) corresponds to ```intrinsic '+'(D1::G3JacHybridPoint, D2::G3JacHybridPoint)```

Inside ```src/general/lpolyBSGS.m```:
- Algorithm 6 (Step 2. Baby-step giant-step harness) and Algorithm 7 (Step-p baby-step giant-step elimination) correspond to ```lPolyWrapper```

Inside ```src/pgroup/```:
- Algorithms 3 and 4 of [Sut10] correspond to ```pGroupDLStar``` and ```pGroupBasis``` in ```pGroup.m```; the Sylow-subgroup verifier (Remark 7.2) to ```sylowVerifier```
- Algorithm 8 (Sylow-subgroup-eliminator) corresponds to ```sylowEliminator``` in ```sylowEliminator.m```

Inside ```src/step4/lpolyModEll.m```:
- Algorithm 9 (Compute $L_p(T) \bmod \ell$) corresponds to ```computeLPolyModEll```, with subroutines ```safeExtensionDegree``` (Definition 8.1), ```attemptToBuildEllTorsion``` and ```lPolyModEllHelper```

## Differences from the paper

- ```lPolyWrapper``` performs one round of Algorithm 6: Algorithm 7 on $J(C)(\mathbb{F}_p)$, then, if several candidates remain, it keeps each candidate $L$ for which $L(-1)\cdot D$ is fixed by Frobenius for one random $D \in J(C)(\mathbb{F}_{p^2})$, instead of running Algorithm 7 on $\mathrm{Im}(F-1)$.
- ```sylowEliminator``` works on $J(C)(\mathbb{F}_p)$ only, without the budget of Remark 7.2, and runs until a single candidate remains.
