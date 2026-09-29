-- Prove2me | solution 1 for ShallowProductCoin.isBox_attains
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:15:31.930564+00:00
-- url     : https://prove2.me/submissions/eefd7043-0c55-43ad-9b95-250743ea006d

-- Sol generated from Applications/ShallowProductCoinRigidity/Core.lean
import Mathlib
import Definitions.Def_Applications_ShallowProductCoinRigidity_Core
import Theorems.Thm_ShallowProductCoin_uniform_isCoin
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






/-! ### Boxes attain the optimum -/

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
/-- The amplitude against a product set factors. -/
theorem bipAmp_product (A₀ : Finset A) (B₀ : Finset B) (f : A → ℂ) (g : B → ℂ) :
    bipAmp (A₀ ×ˢ B₀) f g = (∑ a ∈ A₀, f a) * ∑ b ∈ B₀, g b := by
  unfold bipAmp
  rw [Finset.sum_product, Finset.sum_mul_sum]


omit [Fintype A] in
/-- Total amplitude of the uniform coin over its support. -/
theorem uniform_sum (A₀ : Finset A) (h : A₀.Nonempty) :
    (∑ a ∈ A₀, if a ∈ A₀ then ((Real.sqrt A₀.card : ℝ) : ℂ)⁻¹ else 0)
      = ((Real.sqrt A₀.card : ℝ) : ℂ) := by
  have hc : (0 : ℝ) < (A₀.card : ℝ) := by exact_mod_cast Finset.card_pos.2 h
  have hs : Real.sqrt A₀.card ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  rw [Finset.sum_congr rfl fun a ha => (if_pos ha), Finset.sum_const, nsmul_eq_mul]
  have hsq : ((A₀.card : ℂ)) = ((Real.sqrt A₀.card : ℝ) : ℂ) * ((Real.sqrt A₀.card : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
    simp
  rw [hsq]
  field_simp

omit [Fintype A] [Fintype B] in
/-- A nonempty box is exactly the product of its two projections. -/
theorem isBox_eq_product {R : Finset (A × B)} (hR : IsBox R) :
    R = (R.image Prod.fst) ×ˢ (R.image Prod.snd) := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_product, Finset.mem_image]
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · intro hx
    simp only [Finset.mem_product, Finset.mem_image] at hx
    obtain ⟨⟨y, hy, hy1⟩, ⟨z, hz, hz2⟩⟩ := hx
    have h := hR y hy z hz
    rwa [hy1, hz2] at h


/-! ### The dichotomy -/



open ShallowProductCoin in
theorem solution{R : Finset (A × B)} (hR : IsBox R) (hne : R.Nonempty) :
    ∃ f : A → ℂ, ∃ g : B → ℂ, IsCoin f ∧ IsCoin g ∧ ‖bipAmp R f g‖ ^ 2 = (R.card : ℝ) := by
  classical
  set A₀ := R.image Prod.fst with hA₀
  set B₀ := R.image Prod.snd with hB₀
  have hprod : R = A₀ ×ˢ B₀ := isBox_eq_product hR
  have hA₀ne : A₀.Nonempty := hne.image _
  have hB₀ne : B₀.Nonempty := hne.image _
  have hcA : (0 : ℝ) < (A₀.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hA₀ne
  have hcB : (0 : ℝ) < (B₀.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB₀ne
  refine ⟨fun a => if a ∈ A₀ then ((Real.sqrt A₀.card : ℝ) : ℂ)⁻¹ else 0,
          fun b => if b ∈ B₀ then ((Real.sqrt B₀.card : ℝ) : ℂ)⁻¹ else 0,
          uniform_isCoin A₀ hA₀ne, uniform_isCoin B₀ hB₀ne, ?_⟩
  rw [hprod, bipAmp_product, uniform_sum A₀ hA₀ne, uniform_sum B₀ hB₀ne]
  rw [norm_mul, mul_pow]
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hcA.le, Real.sq_sqrt hcB.le, Finset.card_product]
  push_cast
  ring
