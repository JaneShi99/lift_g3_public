# lift_g3_public
Lifting L polynomials of genus 3 curves

This repository provides a Magma program for "lifting $L$-polynomial of genus 3 curves".

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
