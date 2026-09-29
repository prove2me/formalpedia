-- Prove2me | solution 1 for PowerSumReveal.card_revealing_exponents
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:56:42.923223+00:00
-- url     : https://prove2.me/submissions/d42748fc-fdc5-4674-91f2-b6e9214908b5

-- Sol generated from Geometry/PowerSumFirstHit.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_carmichael_pos
import Theorems.Thm_PowerSumReveal_dvd_carmichael_left
import Theorems.Thm_PowerSumReveal_dvd_carmichael_right
import Theorems.Thm_PowerSumReveal_revealing_eq_sdiff_union

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


/-- Inside `(0, λ]` the multiples of `p-1` and of `q-1` meet only at `λ`. -/
theorem inter_multiples_eq_singleton (hp : p.Prime) (hq : q.Prime) :
    {x ∈ Finset.Ioc 0 (carmichael p q) | (p - 1) ∣ x} ∩
        {x ∈ Finset.Ioc 0 (carmichael p q) | (q - 1) ∣ x}
      = {carmichael p q} := by
  have hpos := carmichael_pos hp hq
  ext k
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨hk0, hkle⟩, hA⟩, ⟨-, hB⟩⟩
    have : carmichael p q ∣ k := Nat.lcm_dvd hA hB
    exact Nat.le_antisymm hkle (Nat.le_of_dvd hk0 this)
  · rintro rfl
    exact ⟨⟨⟨hpos, le_rfl⟩, dvd_carmichael_left⟩, ⟨⟨hpos, le_rfl⟩, dvd_carmichael_right⟩⟩



open PowerSumReveal in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ({k ∈ Finset.Ioc 0 (carmichael p q) |
        Nat.gcd (powerSum (p * q) k) (p * q) ≠ 1 ∧
          Nat.gcd (powerSum (p * q) k) (p * q) ≠ p * q}).card
      = carmichael p q / (p - 1) + carmichael p q / (q - 1) - 2 := by
  classical
  have hA : ({x ∈ Finset.Ioc 0 (carmichael p q) | (p - 1) ∣ x}).card
      = carmichael p q / (p - 1) := Nat.Ioc_filter_dvd_card_eq_div _ _
  have hB : ({x ∈ Finset.Ioc 0 (carmichael p q) | (q - 1) ∣ x}).card
      = carmichael p q / (q - 1) := Nat.Ioc_filter_dvd_card_eq_div _ _
  set A := {x ∈ Finset.Ioc 0 (carmichael p q) | (p - 1) ∣ x} with hAdef
  set B := {x ∈ Finset.Ioc 0 (carmichael p q) | (q - 1) ∣ x} with hBdef
  have hinter : A ∩ B = {carmichael p q} := inter_multiples_eq_singleton hp hq
  have hinter' : B ∩ A = {carmichael p q} := by rw [Finset.inter_comm]; exact hinter
  have e1 : (A \ B).card + 1 = A.card := by
    have := Finset.card_sdiff_add_card_inter A B
    rwa [hinter, Finset.card_singleton] at this
  have e2 : (B \ A).card + 1 = B.card := by
    have := Finset.card_sdiff_add_card_inter B A
    rwa [hinter', Finset.card_singleton] at this
  have hdisj : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  rw [revealing_eq_sdiff_union hp hq hpq, ← hAdef, ← hBdef,
    Finset.card_union_of_disjoint hdisj]
  omega
