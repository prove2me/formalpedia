-- Prove2me | solution 1 for PowerSumReveal.revealing_eq_sdiff_union
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:54:46.635199+00:00
-- url     : https://prove2.me/submissions/274b5e54-ef8a-407e-b6ca-07d3121b452c

-- Sol generated from Geometry/PowerSumFirstHit.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_gcd_powerSum_eq_one_iff
import Theorems.Thm_PowerSumReveal_gcd_powerSum_eq_self_iff

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
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    {k ∈ Finset.Ioc 0 (carmichael p q) |
        Nat.gcd (powerSum (p * q) k) (p * q) ≠ 1 ∧
          Nat.gcd (powerSum (p * q) k) (p * q) ≠ p * q}
      = ({x ∈ Finset.Ioc 0 (carmichael p q) | (p - 1) ∣ x} \
            {x ∈ Finset.Ioc 0 (carmichael p q) | (q - 1) ∣ x}) ∪
          ({x ∈ Finset.Ioc 0 (carmichael p q) | (q - 1) ∣ x} \
            {x ∈ Finset.Ioc 0 (carmichael p q) | (p - 1) ∣ x}) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_filter]
  constructor
  · rintro ⟨hk, h1, h2⟩
    have hk0 : k ≠ 0 := by omega
    rw [Ne, gcd_powerSum_eq_one_iff hp hq hpq hk0, carmichael, Nat.lcm_dvd_iff] at h1
    rw [Ne, gcd_powerSum_eq_self_iff hp hq hpq hk0] at h2
    push_neg at h1 h2
    by_cases hA : (p - 1) ∣ k
    · exact Or.inl ⟨⟨hk, hA⟩, fun h => (h1 hA) h.2⟩
    · exact Or.inr ⟨⟨hk, h2 hA⟩, fun h => hA h.2⟩
  · intro h
    have hk : 0 < k ∧ k ≤ carmichael p q := by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.1
    have hk0 : k ≠ 0 := by omega
    refine ⟨hk, ?_, ?_⟩
    · rw [Ne, gcd_powerSum_eq_one_iff hp hq hpq hk0, carmichael, Nat.lcm_dvd_iff]
      push_neg
      rcases h with ⟨⟨-, hA⟩, hB⟩ | ⟨⟨-, hB⟩, hA⟩
      · intro _; exact fun hb => hB ⟨hk, hb⟩
      · intro ha; exact absurd ⟨hk, ha⟩ hA
    · rw [Ne, gcd_powerSum_eq_self_iff hp hq hpq hk0]
      push_neg
      rcases h with ⟨⟨-, hA⟩, -⟩ | ⟨⟨-, hB⟩, -⟩
      · intro hcon; exact absurd hA hcon
      · intro _; exact hB
