-- Prove2me | solution 1 for Zeta23.MV.norm_B_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:19:03.534177+00:00
-- url     : https://prove2.me/submissions/6020ffde-c9fd-4ecb-b97a-24e235cf02c1

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_MV
import Theorems.Thm_Zeta23_MV_norm_B_le_add

-- from Zeta23.MV
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/MV.lean — the Montgomery–Vaughan weighted Hilbert inequality: literature (diagonal, y = x)
form ⇒ the bilinear (x, z) form H-MV of Zeta23/Hypotheses.lean.

Purpose (trust reduction): Zeta23.MVHilbert C — what [prop:PP]/[prop:cross] consume —
is the BILINEAR inequality |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ C (Σ|x_r|²/δ_r)^{1/2} (Σ|z_r|²/δ_r)^{1/2}.
The published theorem is the case z = x.  The paper, [lem:MV] and its proof,
verbatim: "Lemma (Montgomery–Vaughan). Let λ_1,…,λ_R be distinct real numbers and
δ_r := min_{s≠r}|λ_r−λ_s|. Then for all complex x_r, z_r,
  |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ (3π/2)(Σ_r |x_r|²/δ_r)^{1/2}(Σ_r |z_r|²/δ_r)^{1/2}.
Proof. For z = x this is the weighted ("generalised") Hilbert inequality of Montgomery and Vaughan
[MV74, Theorem 2]; see also [Mon94, Chapter 7]. Any absolute constant in place of 3π/2 would
suffice below. In general, let H be the Hermitian matrix with entries i/(λ_r−λ_s) off the
diagonal and 0 on it, and Δ := diag(δ_r^{1/2}). The case z = x says |y*(ΔHΔ)y| ≤ (3π/2)‖y‖₂² for
all y, i.e. ‖ΔHΔ‖ ≤ 3π/2 since ΔHΔ is Hermitian; hence
|x*Hz| = |(Δ⁻¹x)*(ΔHΔ)(Δ⁻¹z)| ≤ (3π/2)‖Δ⁻¹x‖₂‖Δ⁻¹z‖₂."

Literature statement transcribed (H. L. Montgomery and R. C. Vaughan, "Hilbert's inequality",
J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2 = the "generalised" weighted form, their
(1.8)): if λ_1,…,λ_R are distinct reals, δ_r := min_{s≠r}|λ_r − λ_s|, then for all complex x_r,
  |Σ_{r≠s} x_r x̄_s / (λ_r − λ_s)| ≤ (3π/2) Σ_r |x_r|²/δ_r.
(The constant 3π/2 was later improved — Preissmann 1984 — but the paper says any absolute
constant suffices, and the headline result only needs ∃ C, so C is kept abstract: MVDiag C.)
As in Zeta23.MVHilbert we allow any admissible δ (δ_r > 0, δ_r ≤ |λ_r − λ_s| for s ≠ r); the right
side is antitone in δ, so this is equivalent to the min-gap δ of the literature.

We derive the bilinear form with constant 2C (not C) by POLARIZATION of the sesquilinear form plus
the scaling x ↦ t x, z ↦ z/t — an elementary route that avoids operator norms; the factor 2 is
immaterial (∃ C).  Result: Zeta23.MVHilbert_of_diag : 0 ≤ C → MVDiag C → MVHilbert (2 * C), and
Zeta23.exists_MVHilbert_of_diag for the ∃-forms used by PaperInputs.MV.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23


namespace MV

variable {ι : Type} [Fintype ι] [DecidableEq ι]








omit [DecidableEq ι] in
lemma N2_nonneg {δ : ι → ℝ} (hδ : ∀ r, 0 < δ r) (x : ι → ℂ) : 0 ≤ N2 δ x :=
  sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (hδ r).le

omit [DecidableEq ι] in
lemma eq_zero_of_N2_eq_zero {δ : ι → ℝ} (hδ : ∀ r, 0 < δ r) {x : ι → ℂ} (h : N2 δ x = 0) :
    x = 0 := by
  unfold N2 at h
  have := (sum_eq_zero_iff_of_nonneg (fun r _ => div_nonneg (sq_nonneg _) (hδ r).le)).mp h
  funext r
  have hr := this r (mem_univ r)
  rw [div_eq_zero_iff] at hr
  rcases hr with hr | hr
  · exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hr)
  · exact absurd hr (hδ r).ne'

lemma B_zero_left (freq : ι → ℝ) (z : ι → ℂ) : B freq 0 z = 0 := by simp [B]
lemma B_zero_right (freq : ι → ℝ) (x : ι → ℂ) : B freq x 0 = 0 := by simp [B]

/-- Scaling invariance: B(t x, t⁻¹ z) = B(x, z) for real t ≠ 0. -/
lemma B_scale (freq : ι → ℝ) (x z : ι → ℂ) {t : ℝ} (ht : t ≠ 0) :
    B freq ((t : ℂ) • x) ((t⁻¹ : ℝ) • z) = B freq x z := by
  unfold B
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  have : (t : ℂ) * ((t⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht)]
  linear_combination (x r * conj (z s) * coef freq r s) * this

omit [DecidableEq ι] in
lemma N2_scale (δ : ι → ℝ) (x : ι → ℂ) (t : ℝ) :
    N2 δ ((t : ℂ) • x) = t ^ 2 * N2 δ x := by
  unfold N2
  rw [mul_sum]
  refine sum_congr rfl fun r _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

omit [DecidableEq ι] in
lemma N2_real_smul (δ : ι → ℝ) (x : ι → ℂ) (t : ℝ) :
    N2 δ (t • x) = t ^ 2 * N2 δ x := by
  have : (t • x) = ((t : ℂ) • x) := by funext r; simp [Complex.real_smul]
  rw [this, N2_scale]



end MV



end Zeta23
end
open Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution {C : ℝ} (hC : 0 ≤ C) {freq δ : ι → ℝ} (hδ : ∀ r, 0 < δ r)
    (hdiag : ∀ y : ι → ℂ, ‖B freq y y‖ ≤ C * N2 δ y) (x z : ι → ℂ) :
    ‖B freq x z‖ ≤ 2 * C * Real.sqrt (N2 δ x) * Real.sqrt (N2 δ z) := by
  set u := Real.sqrt (N2 δ x) with hu
  set v := Real.sqrt (N2 δ z) with hv
  have hNx := N2_nonneg hδ x
  have hNz := N2_nonneg hδ z
  by_cases hx0 : N2 δ x = 0
  · rw [eq_zero_of_N2_eq_zero hδ hx0, B_zero_left, norm_zero]; positivity
  by_cases hz0 : N2 δ z = 0
  · rw [eq_zero_of_N2_eq_zero hδ hz0, B_zero_right, norm_zero]; positivity
  have hu0 : 0 < u := Real.sqrt_pos.mpr (lt_of_le_of_ne hNx (Ne.symm hx0))
  have hv0 : 0 < v := Real.sqrt_pos.mpr (lt_of_le_of_ne hNz (Ne.symm hz0))
  have hu2 : u ^ 2 = N2 δ x := Real.sq_sqrt hNx
  have hv2 : v ^ 2 = N2 δ z := Real.sq_sqrt hNz
  -- t with t² = v/u
  set t := Real.sqrt (v / u) with htdef
  have ht2 : t ^ 2 = v / u := Real.sq_sqrt (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have hscale := B_scale freq x z ht0.ne'
  rw [← hscale]
  refine (norm_B_le_add hC hdiag _ _).trans ?_
  rw [N2_scale, N2_real_smul, inv_pow, ht2, ← hu2, ← hv2]
  have : v / u * u ^ 2 + (v / u)⁻¹ * v ^ 2 = 2 * (u * v) := by
    field_simp
    ring
  rw [this]
  exact le_of_eq (by ring)
