-- Prove2me | solution 1 for Bridges.AlexanderTorus.recover_factors_from_degrees
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:59:41.893823+00:00
-- url     : https://prove2.me/submissions/dff9542a-7d84-4a74-b520-257a3c89263c

-- Sol generated from Bridges/AlexanderKnotNumberBridge.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
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

/-- `φ(pq) = (p-1)(q-1)` and `p + q = pq + 1 - φ(pq)`. -/
theorem totient_semiprime_and_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Nat.totient (p * q) = (p - 1) * (q - 1) ∧
    p + q = p * q + 1 - Nat.totient (p * q) := by
  have ht : Nat.totient (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hne), Nat.totient_prime hp,
      Nat.totient_prime hq]
  refine ⟨ht, ?_⟩
  rw [ht]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp.one_lt.le
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq.one_lt.le
  have h : (1 + a) * (1 + b) = 1 + (a + b + a * b) := by ring
  simp only [Nat.add_sub_cancel_left, h]
  omega


/-! ## Irreducibility of `A_N` characterizes primality of `N` -/





open Bridges.AlexanderTorus in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q)
    (s : ℕ) (hs : s = p * q + 1 - Nat.totient (p * q)) :
    (s - Nat.sqrt (s ^ 2 - 4 * (p * q))) / 2 = p ∧
    (s + Nat.sqrt (s ^ 2 - 4 * (p * q))) / 2 = q := by
  obtain ⟨-, hsum⟩ := totient_semiprime_and_sum hp hq hlt.ne
  have hspq : s = p + q := by omega
  have hdisc : s ^ 2 - 4 * (p * q) = (q - p) ^ 2 := by
    rw [hspq]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
    have h : (p + (p + c)) ^ 2 = c ^ 2 + 4 * (p * (p + c)) := by ring
    simp only [Nat.add_sub_cancel_left]
    omega
  rw [hdisc, Nat.sqrt_eq']
  omega
