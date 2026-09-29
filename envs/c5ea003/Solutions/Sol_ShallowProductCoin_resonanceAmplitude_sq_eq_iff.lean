-- Prove2me | solution 1 for ShallowProductCoin.resonanceAmplitude_sq_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:18:03.198473+00:00
-- url     : https://prove2.me/submissions/afac737d-5725-4d8a-9671-ac5be12881ff

-- Sol generated from Applications/ShallowProductCoinRigidity/Core.lean
import Mathlib
import Definitions.Def_Applications_ShallowProductCoinRigidity_Core
import Theorems.Thm_ShallowProductCoin_gap_of_rankOne
import Theorems.Thm_ShallowProductCoin_isBox_attains
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



/-! ### The gap for real rank-one vectors -/


/-! ### From real rank-one vectors to complex product coins -/

omit [DecidableEq A] [DecidableEq B] in
/-- A product of two normalised modulus vectors is normalised on `A × B`. -/
theorem prod_norm_sq (p : A → ℝ) (q : B → ℝ) (hp1 : ∑ a, p a ^ 2 = 1)
    (hq1 : ∑ b, q b ^ 2 = 1) : ∑ x : A × B, (p x.1 * q x.2) ^ 2 = 1 := by
  have h : ∑ x : A × B, (p x.1 * q x.2) ^ 2 = (∑ a, p a ^ 2) * ∑ b, q b ^ 2 := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h, hp1, hq1, mul_one]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
/-- The complex amplitude is dominated by the amplitude of the modulus coin. -/
theorem norm_bipAmp_le (R : Finset (A × B)) (f : A → ℂ) (g : B → ℂ) :
    ‖bipAmp R f g‖ ≤ ∑ x ∈ R, ‖f x.1‖ * ‖g x.2‖ := by
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl fun x _ => norm_mul _ _


/-- **Main rigidity gap.**  If `R` is not a box — witnessed by `(a,b), (a',b') ∈ R`
with `(a,b') ∉ R` — then *every* product coin satisfies
`‖A(ψ)‖² · (3|R| + 1) ≤ 3|R|²`, i.e. `‖A(ψ)‖² ≤ (1 - 1/(3|R|+1))·|R|`. -/
theorem bipAmp_sq_gap (R : Finset (A × B)) (f : A → ℂ) (g : B → ℂ)
    (hf : IsCoin f) (hg : IsCoin g) {a a' : A} {b b' : B}
    (hab : (a, b) ∈ R) (hab' : (a', b') ∈ R) (hout : (a, b') ∉ R) :
    ‖bipAmp R f g‖ ^ 2 * (3 * R.card + 1) ≤ 3 * (R.card : ℝ) ^ 2 := by
  set u : A × B → ℝ := fun x => ‖f x.1‖ * ‖g x.2‖ with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hu1 : ∑ x : A × B, u x ^ 2 = 1 := prod_norm_sq _ _ hf hg
  have hrank : u (a, b) * u (a', b') = u (a, b') * u (a', b) := by simp [hu]; ring
  have hgap := gap_of_rankOne R u hu0 hu1 hrank hab hab' hout
  have hT : ‖bipAmp R f g‖ ≤ ∑ x ∈ R, u x := norm_bipAmp_le R f g
  have h0 : (0 : ℝ) ≤ ‖bipAmp R f g‖ := norm_nonneg _
  have h1 : ‖bipAmp R f g‖ ^ 2 ≤ (∑ x ∈ R, u x) ^ 2 := by nlinarith [hT, h0]
  have hpos : (0 : ℝ) ≤ 3 * (R.card : ℝ) + 1 := by positivity
  nlinarith [hgap, h1, hpos]


/-! ### Boxes attain the optimum -/






/-! ### The dichotomy -/



open ShallowProductCoin in
theorem solution{R : Finset (A × B)} (hne : R.Nonempty) :
    (∃ f : A → ℂ, ∃ g : B → ℂ, IsCoin f ∧ IsCoin g ∧ ‖bipAmp R f g‖ ^ 2 = (R.card : ℝ))
      ↔ IsBox R := by
  refine ⟨fun ⟨f, g, hf, hg, heq⟩ => ?_, fun hR => isBox_attains hR hne⟩
  by_contra hbox
  unfold IsBox at hbox
  push_neg at hbox
  obtain ⟨x, hx, y, hy, hxy⟩ := hbox
  have hgap := bipAmp_sq_gap R f g hf hg (a := x.1) (b := x.2) (a' := y.1) (b' := y.2)
    (by simpa using hx) (by simpa using hy) hxy
  rw [heq] at hgap
  have hm1 : (1 : ℝ) ≤ (R.card : ℝ) := by
    have h : 1 ≤ R.card := Finset.card_pos.2 hne
    exact_mod_cast h
  nlinarith [hgap, hm1]
