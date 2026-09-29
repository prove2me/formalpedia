-- Prove2me | solution 1 for Bridges.AlexanderTorus.cyclotomic_two_mul_semiprime_eval_neg_one_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T20:25:06.243562+00:00
-- url     : https://prove2.me/submissions/8d6ed2c7-5ea0-4b67-9d1a-c1c62589c14b

-- Sol generated from Bridges/AlexanderKnotNumberBridgeVI.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_cyclotomic_two_mul_eval_neg_one
/-
# The knot–number bridge VI: the local–global factorization of the knot determinant

Cycle II of this thread computed the "local determinants" `Φ_{2d}(-1)` in two special
cases (`d` prime and `d` a product of two distinct primes) by dividing the global
determinant `A_N(-1) = N` by the other factors.  This file proves the *general* local–global
statement conjectured as `C2` in `FUTURE_DIRECTIONS.md`:

* `Bridges.AlexanderTorus.cyclotomic_two_mul_eval_neg_one` :
  for odd `n > 0`, `Φ_{2n}(-1) = Φ_n(1)`.  This is proved by strong induction from the two
  divisor-product identities
  `∏_{d ∣ n, d > 1} Φ_{2d} = A_n` (the knot side, cycle I) and
  `∏_{d ∣ n, d > 1} Φ_d = 1 + X + ⋯ + X^{n-1}` (the classical side),
  evaluated at `-1` and `1` respectively — both give `n`.
* `Bridges.AlexanderTorus.cyclotomic_two_mul_prime_pow_eval_neg_one` :
  `Φ_{2p^{k+1}}(-1) = p` for an odd prime `p`.
* `Bridges.AlexanderTorus.cyclotomic_two_mul_eval_neg_one_of_not_isPrimePow` :
  `Φ_{2d}(-1) = 1` if `d > 1` is odd and not a prime power.
* `Bridges.AlexanderTorus.knot_determinant_local_global` :
  `∏_{d ∣ N, d > 1} Φ_{2d}(-1) = N`, i.e. the determinant of `T(2,N)` is the product of the
  local determinants; combined with the two previous results, the only divisors contributing
  a nontrivial local determinant are the prime powers `p^j ∣ N`, each contributing `p`.
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The two divisor-product identities, evaluated -/



/-! ## `Φ_{2n}(-1) = Φ_n(1)` for odd `n` -/


/-! ## The local determinants -/


/-- The local determinant is trivial away from prime powers: `Φ_{2d}(-1) = 1` for odd `d > 1`
which is not a prime power. -/
theorem cyclotomic_two_mul_eval_neg_one_of_not_isPrimePow {d : ℕ} (hd : Odd d) (h1 : 1 < d)
    (hpp : ¬ IsPrimePow d) : (cyclotomic (2 * d) ℤ).eval (-1) = 1 := by
  rw [cyclotomic_two_mul_eval_neg_one d hd (by omega)]
  refine eval_one_cyclotomic_not_prime_pow ?_
  intro p hp k hk
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp at hk; omega
    · exact hk'
  exact hpp ⟨p, k, hp.prime, hkpos, hk⟩

/-! ## Consequences: the cycle II computations, generalized -/




open Bridges.AlexanderTorus in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    (cyclotomic (2 * (p * q)) ℤ).eval (-1) = 1 := by
  have h1 : 1 < p * q := by nlinarith [hp.one_lt, hq.one_lt]
  refine cyclotomic_two_mul_eval_neg_one_of_not_isPrimePow (hpo.mul hqo) h1 ?_
  rintro ⟨r, k, hr, hk, hrk⟩
  have hpq0 : p * q ≠ 0 := by positivity
  have hfac : (p * q).primeFactors = {r} := by
    rw [← hrk, Nat.primeFactors_pow _ hk.ne', hr.nat_prime.primeFactors]
  have hpm : p ∈ (p * q).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, dvd_mul_right p q, hpq0⟩
  have hqm : q ∈ (p * q).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hq, dvd_mul_left q p, hpq0⟩
  rw [hfac, Finset.mem_singleton] at hpm hqm
  exact hne (hpm.trans hqm.symm)
