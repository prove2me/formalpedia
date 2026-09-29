-- Prove2me | solution 2 for Bridges.AlexanderTorus.alexander_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-19T22:23:00.716787+00:00
-- url     : https://prove2.me/submissions/7799ddc3-c92c-4fcd-ba7f-663e4842d37c

-- Sol generated from Bridges/AlexanderKnotNumberBridge.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_X_add_one_mul_alexander_odd
import Theorems.Thm_Bridges_AlexanderTorus_alexander_ne_zero
/-
# A Knot–Number Theory Bridge: the Alexander polynomial of the torus knot `T(2,N)`

The Alexander polynomial of the `(2,N)` torus knot is (up to normalization)

  `A_N(X) = (X^N + 1) / (X + 1) = ∑_{i < N} (-1)^i X^i`   (`N` odd).

This file proves that `A_N` is, over `ℤ`, the product of the cyclotomic polynomials
`Φ_{2d}` for the divisors `d > 1` of `N`; in particular the *multiset of degrees of
its irreducible factors* is `{φ(d) : d ∣ N, d > 1}`, which for a semiprime `N = pq`
is `{p-1, q-1, (p-1)(q-1)}`, from which `φ(N)`, `p+q` and finally `p, q` are recovered.

Main results:

* `Bridges.AlexanderTorus.prod_cyclotomic_two_mul_divisors` :
  `∏_{d ∣ N} Φ_{2d} = X^N + 1` for odd `N > 0`.
* `Bridges.AlexanderTorus.alexander_eq_prod_cyclotomic` :
  `A_N = ∏_{d ∣ N, d ≠ 1} Φ_{2d}`.
* `Bridges.AlexanderTorus.alexander_semiprime_factorization` :
  `A_{pq} = Φ_{2p} · Φ_{2q} · Φ_{2pq}` for distinct odd primes `p ≠ q`, together with
  `alexander_semiprime_factor_data`: irreducibility of the three factors and their
  degrees `p-1`, `q-1`, `(p-1)(q-1)`.
* `Bridges.AlexanderTorus.alexander_irreducible_iff_prime` :
  for odd `N > 1`, `A_N` is irreducible over `ℤ` **iff** `N` is prime.
* `Bridges.AlexanderTorus.recover_factors_from_degrees` :
  the two primes are recovered from the degree data by
  `p = (s - √(s² - 4N))/2`, `q = (s + √(s² - 4N))/2` with `s = N + 1 - φ(N)`.
* `Bridges.AlexanderTorus.knot_determinant` : `A_N(-1) = N`
  (the determinant of the torus knot `T(2,N)`), and
  `alexander_natDegree` : `deg A_N = N - 1` (the "catch": exponential size in `log N`).
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The Alexander polynomial of `T(2,N)` -/







/-! ## Elementary divisor combinatorics -/




/-! ## The cyclotomic factorization -/



/-! ## Degree of `A_N` (the "catch": exponential in `log N`) -/


/-! ## Knot determinant -/



/-! ## Semiprimes -/



/-! ## Degrees of the irreducible factors -/






/-! ## Recovering the factorization from the degree data -/



/-! ## Irreducibility of `A_N` characterizes primality of `N` -/





open Bridges.AlexanderTorus in
theorem solution{N : ℕ} (hN : Odd N) : (alexander N).natDegree = N - 1 := by
  have hpos : 0 < N := hN.pos
  have h := X_add_one_mul_alexander_odd hN
  have hX1 : (X + 1 : ℤ[X]) ≠ 0 := fun hc => by
    simpa using congrArg (Polynomial.eval 0) hc
  have hdeg : ((X + 1 : ℤ[X]) * alexander N).natDegree
      = (X + 1 : ℤ[X]).natDegree + (alexander N).natDegree :=
    natDegree_mul hX1 (alexander_ne_zero hN)
  have hXd : (X + 1 : ℤ[X]).natDegree = 1 := by
    simpa using natDegree_X_add_C (1 : ℤ)
  have hR : ((X : ℤ[X]) ^ N + 1).natDegree = N := by
    have hC : ((X : ℤ[X]) ^ N + 1) = (X ^ N + C 1) := by simp
    rw [hC, natDegree_X_pow_add_C]
  rw [h, hR, hXd] at hdeg
  omega
