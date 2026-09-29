-- Prove2me | solution 1 for ShallowProductCoin.gap_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:14:03.530176+00:00
-- url     : https://prove2.me/submissions/d10bf34c-b5b6-4405-9b47-9f29f2156c23

-- Sol generated from Applications/ShallowProductCoinRigidity/Core.lean
import Mathlib
import Definitions.Def_Applications_ShallowProductCoinRigidity_Core
/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/

/-!
# Rigidity gap for shallow product coins — the bipartite core

## Setting

Fix two finite "registers" `A` and `B` and a *resonance set* `R ⊆ A × B`.
A **coin** on a finite register is an `ℓ²`-normalised complex amplitude vector,
`∑ a, ‖f a‖² = 1`.  The **resonance amplitude** of the *product coin* `f ⊗ g` is

`bipAmp R f g = ∑ x ∈ R, f x.1 * g x.2`.

The elementary Cauchy–Schwarz bound is `‖bipAmp R f g‖² ≤ |R|`
(`bipAmp_sq_le_card`), with equality forcing the product coin to be the
normalised indicator of `R`.  The content of this file is the *quantitative*
converse:

**Main theorem** (`bipAmp_sq_gap`).  If `R` is **not** a combinatorial box, then
for *every* product coin

`‖bipAmp R f g‖² · (3|R| + 1) ≤ 3|R|²`,  i.e.  `‖A(ψ)‖² ≤ (1 - 1/(3|R|+1))·|R|`,

an explicit multiplicative deficiency depending only on `|R|`; in additive form
`‖A(ψ)‖² ≤ |R| - 2/7` (`bipAmp_sq_le_card_sub`).

Combined with the fact that a box *does* attain the optimum
(`isBox_attains`), this yields the exact dichotomy
`resonanceAmplitude_sq_eq_iff`: the optimum `|R|` is attained by a product coin
**iff** `R` is a box.

## Proof idea

Write `u = |f| ⊗ |g|` for the modulus product vector, `T = ∑_{x∈R} u x`,
`m = |R|` and `μ = T/m`.  A direct expansion gives

`∑_{x} (u x - μ·1_R x)² = 1 - T²/m`.

If `R` is not a box there are `(a,b), (a',b') ∈ R` with `(a,b') ∉ R`, and the
four points `(a,b), (a,b'), (a',b), (a',b')` are pairwise distinct.  The `2 × 2`
minor of `u` at these points vanishes (`u` has rank one), while the
corresponding minor of `μ·1_R` equals `μ²`.  Comparing the two minors through
the four deviations `e₁₁, e₁₂, e₂₁, e₂₂` and an AM–GM step
(`rankOne_minor_ineq`) gives `μ² ≤ 3(e₁₁²+e₁₂²+e₂₁²+e₂₂²) ≤ 3(1 - T²/m)`, i.e.
`T²/m² ≤ 3 - 3T²/m`, which is exactly `T²(3m+1) ≤ 3m²`.  No singular-value
theory is needed.
-/

open Finset

open ShallowProductCoin

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]




/-! ### Two elementary ingredients -/

/-- The algebraic heart of the gap.  If a vanishing `2 × 2` minor of a rank-one
matrix is compared with the minor `μ²` of a `0/1` pattern through the four
deviations `e₁₁, e₁₂, e₂₁, e₂₂`, then `μ² ≤ 3·(e₁₁²+e₁₂²+e₂₁²+e₂₂²)`.

The hypothesis `hid` is the vanishing of the rank-one minor written in terms of
the deviations; `c ≤ 1` bounds the (unknown) value of the pattern at the fourth
point, and `mu`, `e₁₂` are nonnegative because the underlying vector is a
product of moduli.

The optimal constant here is `φ² = (3+√5)/2 = 2.618…`, attained at
`(e₁₁,e₁₂,e₂₁,e₂₂) = (-1,√5,1,-1)·(√5-2)/…`; the value `3` used below is a
convenient rational relaxation. -/
theorem rankOne_minor_ineq (mu c e11 e12 e21 e22 : ℝ) (hmu : 0 ≤ mu) (he12 : 0 ≤ e12)
    (hc1 : c ≤ 1)
    (hid : mu ^ 2 + mu * (e11 + e22) + e11 * e22 - mu * c * e12 - e12 * e21 = 0) :
    mu ^ 2 ≤ 3 * (e11 ^ 2 + e12 ^ 2 + e21 ^ 2 + e22 ^ 2) := by
  nlinarith [sq_nonneg (mu + e11 + e22), sq_nonneg (e11 - e22), sq_nonneg (e12 - e21),
    sq_nonneg (mu - 2 * e12), sq_nonneg (mu + 2 * e11), sq_nonneg (mu + 2 * e22),
    mul_nonneg hmu he12, mul_nonneg hmu (mul_nonneg he12 (sub_nonneg.2 hc1)),
    sq_nonneg (e11 + e22 + e12)]

/-- Four values of a nonnegative function at the four corners of a
combinatorial rectangle are dominated by the total sum. -/
theorem sum_four_le (F : A × B → ℝ) (hF : ∀ x, 0 ≤ F x) {a a' : A} {b b' : B}
    (ha : a ≠ a') (hb : b ≠ b') :
    F (a, b) + F (a, b') + F (a', b) + F (a', b') ≤ ∑ x : A × B, F x := by
  have hsub : ({(a, b), (a, b'), (a', b), (a', b')} : Finset (A × B)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hF x)
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_insert (by simp [ha, hb]), Finset.sum_insert (by simp [ha, Ne.symm hb]),
    Finset.sum_insert (by simp [hb])]
  simp
  ring

/-! ### The gap for real rank-one vectors -/


/-! ### From real rank-one vectors to complex product coins -/






/-! ### Boxes attain the optimum -/






/-! ### The dichotomy -/



open ShallowProductCoin in
theorem solution(R : Finset (A × B)) (u : A × B → ℝ) (hu0 : ∀ x, 0 ≤ u x)
    (hu1 : ∑ x : A × B, u x ^ 2 = 1)
    {a a' : A} {b b' : B}
    (hrank : u (a, b) * u (a', b') = u (a, b') * u (a', b))
    (hab : (a, b) ∈ R) (hab' : (a', b') ∈ R) (hout : (a, b') ∉ R) :
    (∑ x ∈ R, u x) ^ 2 * (3 * R.card + 1) ≤ 3 * (R.card : ℝ) ^ 2 := by
  have ha : a ≠ a' := by rintro rfl; exact hout hab'
  have hb : b ≠ b' := by rintro rfl; exact hout hab
  set m : ℝ := (R.card : ℝ) with hm
  have hm1 : 1 ≤ m := by
    have h : 1 ≤ R.card := Finset.card_pos.2 ⟨_, hab⟩
    simpa [hm] using (Nat.one_le_cast (α := ℝ)).2 h
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  set T : ℝ := ∑ x ∈ R, u x with hT
  set mu : ℝ := T / m with hmu
  set ind : A × B → ℝ := fun x => if x ∈ R then (1 : ℝ) else 0 with hind
  -- squared distance from `u` to the best multiple of the indicator of `R`
  have hD : ∑ x : A × B, (u x - mu * ind x) ^ 2 = 1 - 2 * mu * T + mu ^ 2 * m := by
    have h1 : ∀ x : A × B, (u x - mu * ind x) ^ 2
        = u x ^ 2 - 2 * mu * (if x ∈ R then u x else 0)
          + mu ^ 2 * (if x ∈ R then (1 : ℝ) else 0) := by
      intro x; by_cases hx : x ∈ R <;> simp [hind, hx]; ring
    rw [Finset.sum_congr rfl (fun x _ => h1 x)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_ite_mem, Finset.univ_inter, hu1]
    simp [hT, hm]
  have hDval : ∑ x : A × B, (u x - mu * ind x) ^ 2 = 1 - T ^ 2 / m := by
    rw [hD, hmu]; field_simp; ring
  have hfour := sum_four_le (fun x => (u x - mu * ind x) ^ 2) (fun x => sq_nonneg _) ha hb
  have hi1 : ind (a, b) = 1 := by simp [hind, hab]
  have hi2 : ind (a, b') = 0 := by simp [hind, hout]
  have hi4 : ind (a', b') = 1 := by simp [hind, hab']
  have hc1 : ind (a', b) ≤ 1 := by rw [hind]; dsimp only; split <;> norm_num
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => hu0 x
  have hmu0 : 0 ≤ mu := div_nonneg hT0 (le_of_lt hm0)
  have hkey : mu ^ 2 ≤ 3 * ((u (a, b) - mu) ^ 2 + (u (a, b')) ^ 2
      + (u (a', b) - mu * ind (a', b)) ^ 2 + (u (a', b') - mu) ^ 2) :=
    rankOne_minor_ineq _ _ _ _ _ _ hmu0 (hu0 _) hc1 (by linear_combination hrank)
  have hS : (u (a, b) - mu) ^ 2 + (u (a, b')) ^ 2
      + (u (a', b) - mu * ind (a', b)) ^ 2 + (u (a', b') - mu) ^ 2 ≤ 1 - T ^ 2 / m := by
    rw [← hDval]
    calc (u (a, b) - mu) ^ 2 + (u (a, b')) ^ 2
          + (u (a', b) - mu * ind (a', b)) ^ 2 + (u (a', b') - mu) ^ 2
        = (u (a, b) - mu * ind (a, b)) ^ 2 + (u (a, b') - mu * ind (a, b')) ^ 2
          + (u (a', b) - mu * ind (a', b)) ^ 2 + (u (a', b') - mu * ind (a', b')) ^ 2 := by
          rw [hi1, hi2, hi4]; ring
      _ ≤ _ := hfour
  have hmu2 : mu ^ 2 = T ^ 2 / m ^ 2 := by rw [hmu]; ring
  have hlast : T ^ 2 / m ^ 2 ≤ 3 * (1 - T ^ 2 / m) := by rw [← hmu2]; linarith [hkey, hS]
  have hne : m ≠ 0 := ne_of_gt hm0
  have e1 : m ^ 2 * (T ^ 2 / m ^ 2) = T ^ 2 := by field_simp
  have e2 : m ^ 2 * (3 * (1 - T ^ 2 / m)) = 3 * m ^ 2 - 3 * m * T ^ 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left hlast (sq_nonneg m)
  rw [e1, e2] at h3
  nlinarith [h3]
