-- Prove2me | solution 2 for Bridges.AlexanderTorus.alexander_semiprime_factorization
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-19T22:33:42.686353+00:00
-- url     : https://prove2.me/submissions/3c8287e8-971c-4c3c-abf0-d1a6f09a2215

-- Sol generated from Bridges/AlexanderKnotNumberBridge.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_alexander_eq_prod_cyclotomic
import Theorems.Thm_Bridges_AlexanderTorus_divisors_semiprime
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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    alexander (p * q)
      = cyclotomic (2 * p) ℤ * cyclotomic (2 * q) ℤ * cyclotomic (2 * (p * q)) ℤ := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hN : Odd (p * q) := hpo.mul hqo
  have h1 : 1 < p * q := by nlinarith
  rw [alexander_eq_prod_cyclotomic hN h1, divisors_semiprime hp hq]
  have hpq : p ≠ p * q := by nlinarith
  have hqq : q ≠ p * q := by nlinarith
  have herase : ({1, p, q, p * q} : Finset ℕ).erase 1 = {p, q, p * q} := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, rfl | rfl | rfl | rfl⟩ <;> simp_all
    · rintro (rfl | rfl | rfl) <;> exact ⟨by omega, by simp⟩
  rw [herase, Finset.prod_insert (by simp [hne, hpq]), Finset.prod_insert (by simp [hqq]),
    Finset.prod_singleton, mul_assoc]
