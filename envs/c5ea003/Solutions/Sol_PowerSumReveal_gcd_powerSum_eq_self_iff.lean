-- Prove2me | solution 1 for PowerSumReveal.gcd_powerSum_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:52:40.512972+00:00
-- url     : https://prove2.me/submissions/769d9a86-08c6-4d55-8b61-35f224fe2912

-- Sol generated from Geometry/PowerSumFirstHit.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_gcd_powerSum_semiprime

/-!
# Cycle 2: the first hit, an unconditional reveal, and the density of good exponents

The master formula of `Geometry.PowerSumFactorReveal` says that, for `N = p*q` with
`p ≠ q` prime and `k ≥ 1`,

`gcd (powerSum N k) N = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`.

Three consequences are proved here.

* **Unconditional reveal.**  If `p < q` then the side condition `(q-1) ∤ (p-1)` of
  Theorem 1 is *automatic*, so `gcd (powerSum N (p-1)) N = q` with no extra hypothesis.
  (This strengthens the original statement of Theorem 1.)
* **First hit.**  The least exponent `k ≥ 1` at which the gcd is not the trivial value
  `N` is exactly `k* = min (p-1) (q-1)`, and `(k*+1)^2 ≤ N`, i.e. `k* < √N`.
  At `k = k*` the gcd is already a *proper* factor.
* **Density of good exponents.**  Inside one Carmichael period `λ = lcm (p-1) (q-1)`
  the number of exponents that reveal a proper factor is exactly
  `λ/(p-1) + λ/(q-1) - 2`.  So the useful exponents are a `(1/(p-1) + 1/(q-1))`-fraction
  of the period: sparse, which is the quantitative form of the "period-finding barrier".

## Main results

* `PowerSumReveal.gcd_powerSum_eq_self_iff`
* `PowerSumReveal.powerSum_factor_reveal_of_lt` — unconditional Theorem 1.
* `PowerSumReveal.first_hit_isLeast` — first hit at `min (p-1) (q-1)`.
* `PowerSumReveal.first_hit_sq_le` — `k* < √N`.
* `PowerSumReveal.card_revealing_exponents` — density inside one period.
-/

open PowerSumReveal

open Finset

variable {p q : ℕ}

/-! ## A value table for the gcd -/


/-! ## The unconditional reveal at the smaller exponent -/



/-! ## The first hit -/




/-! ## Density of revealing exponents inside one period -/





open PowerSumReveal in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {k : ℕ}
    (hk : k ≠ 0) :
    Nat.gcd (powerSum (p * q) k) (p * q) = p * q ↔ (¬ (p - 1) ∣ k ∧ ¬ (q - 1) ∣ k) := by
  have h2 := hp.two_le
  have h3 := hq.two_le
  rw [gcd_powerSum_semiprime hp hq hpq hk]
  constructor
  · intro h
    by_cases hA : (p - 1) ∣ k
    · exfalso
      by_cases hB : (q - 1) ∣ k
      · rw [if_pos hA, if_pos hB, one_mul] at h; nlinarith
      · rw [if_pos hA, if_neg hB, one_mul] at h; nlinarith
    · by_cases hB : (q - 1) ∣ k
      · exfalso; rw [if_neg hA, if_pos hB, mul_one] at h; nlinarith
      · exact ⟨hA, hB⟩
  · rintro ⟨hA, hB⟩
    rw [if_neg hA, if_neg hB]
