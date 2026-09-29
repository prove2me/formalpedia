-- Prove2me | solution 2 for Bridges.AlexanderTorus.alexander_eq_prod_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-19T22:21:49.311533+00:00
-- url     : https://prove2.me/submissions/2c476c77-4eed-4be5-bdb1-83fe9b081a84

-- Sol generated from Bridges/AlexanderKnotNumberBridge.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_X_add_one_mul_alexander_odd
import Theorems.Thm_Bridges_AlexanderTorus_prod_cyclotomic_two_mul_divisors
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
theorem solution{N : ℕ} (hN : Odd N) (h1 : 1 < N) :
    alexander N = ∏ d ∈ N.divisors.erase 1, cyclotomic (2 * d) ℤ := by
  have hpos : 0 < N := by omega
  have hmem : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.2 hpos.ne'
  have hsplit := Finset.mul_prod_erase _ (fun d => cyclotomic (2 * d) ℤ) hmem
  rw [prod_cyclotomic_two_mul_divisors hN hpos] at hsplit
  simp only [mul_one, cyclotomic_two] at hsplit
  have hne : (X + 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  refine mul_left_cancel₀ hne ?_
  rw [X_add_one_mul_alexander_odd hN, ← hsplit]
