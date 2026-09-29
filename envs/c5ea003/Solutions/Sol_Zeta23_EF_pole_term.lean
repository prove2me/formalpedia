-- Prove2me | solution 1 for Zeta23.EF.pole_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:53:21.991805+00:00
-- url     : https://prove2.me/submissions/5029f907-5e3d-4e23-83e9-434386a17276

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Theorems.Thm_Zeta23_EF_integrable_exp_neg_abs_half_mul
import Theorems.Thm_Zeta23_EF_integrable_inversion_kernel
import Theorems.Thm_Zeta23_EF_integral_EL_mul
import Theorems.Thm_Zeta23_EF_integral_exp_neg_abs_half
import Theorems.Thm_Zeta23_EF_paper_inversion

-- from Zeta23.ExplicitFormula
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula.lean  —  the explicit formula, normalisations (paper App. A [app:EF]).

The *normalisation chain*: the passage from a literature-verbatim explicit formula to the paper's
density ν_X = μ + Π_X + P_X [eq:mudef]–[eq:nudef], with every 2π and every sign:

  * `EF.literatureRHS` / `EF_lit` : the right-hand side of [eq:EFstd] (App. A, first display), i.e. the
    Weil explicit formula in the form the paper quotes from [IK04, Thm 5.12] / [Wei52] / [Bom00],
    for a single test function k ∈ C_c²(ℝ) with h(z) := ∫ k(u) e^{izu} du;
  * `EF.prop_EF_of_lit` : [eq:EFstd] for k := f ⋆ g̃  ⟹  [eq:EF]  W(f,g) = ∫ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ,
    X = e^L, for f, g ∈ C_c²(ℝ) supported in [−L/2, L/2]  — exactly App. A's three identifications
    (Gamma term, prime term, pole term) plus h_{f⋆g̃}(z) = h_f(z)·conj(h_g(conj z)).

The truth of [eq:EFstd] itself (contour integration of
h((s-1/2)/i)·ξ'/ξ(s)) is the hypothesis `EF_lit`, stated for the zero configuration
abstractly.

CONVENTIONS (paper [Notation]).  Paper Fourier transform:
    f̂(τ) = h_f(τ) := ∫_ℝ f(u) e^{iτu} du,   inversion  f(u) = (1/2π) ∫_ℝ h_f(r) e^{-iru} dr.
Mathlib: 𝓕 f w = ∫ v, exp(-2πi v w) • f v.  Dictionary (proved below, `paperFT_ofReal_eq_fourier`):
    h_f(τ) = 𝓕 f (-τ/(2π)).
-/

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-! ### App. A objects owned by this file -/



end EF


namespace EF

/-! ## The literature form [eq:EFstd] -/





/-! ## ℂ-specialised integral helpers

(In this toolchain `rw [← integral_const_mul]` fails to key-match on ℂ-valued integrals because the
RCLike-generic lemma elaborates `Mul ℂ`/`NormedAddCommGroup ℂ` through a different instance path than
a goal written with `*`; restating the lemmas at ℂ (proved by `exact`) makes `rw` usable.) -/

theorem cintegral_const_mul (c : ℂ) (f : ℝ → ℂ) : ∫ x, c * f x = c * ∫ x, f x :=
  integral_const_mul c f

theorem cintegral_mul_const (c : ℂ) (f : ℝ → ℂ) : ∫ x, f x * c = (∫ x, f x) * c :=
  integral_mul_const c f


/-! ## Dictionary with Mathlib's Fourier transform -/




/-! ## The test function k = f ⋆ g̃ -/










/-! ## App. A: the three identifications -/


/-- Compact support from a support bound. -/
theorem hasCompactSupport_of_tsupport_subset {k : ℝ → ℂ} {L : ℝ}
    (hks : tsupport k ⊆ Icc (-L) L) : HasCompactSupport k :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport k) hks






/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/



/-- App. A, "inserting `k(u) = (1/2π)∫ h(τ)e^{−iτu}dτ` and interchanging (all integrals absolutely
convergent)": for an integrable weight E,  `∫ k(u)E(u)du = (1/2π) ∫ h(τ) (∫ E(u)e^{−iτu}du) dτ`. -/
theorem integral_k_mul_weight {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) {E : ℝ → ℂ} (hE : Integrable E) :
    ∫ u : ℝ, k u * E u
      = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ * ∫ u : ℝ, E u * cexp (-I * τ * u) := by
  have hsub : (fun u : ℝ => k u * E u)
      = fun u : ℝ => (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ * cexp (-I * τ * u) * E u := by
    ext u; rw [paper_inversion hk hki hFk u, mul_assoc, ← cintegral_mul_const]
  rw [hsub, cintegral_const_mul]
  congr 1
  rw [integral_integral_swap (integrable_inversion_kernel hFk hE)]
  congr 1; ext τ
  rw [← cintegral_const_mul]
  congr 1; ext u; ring

/-- The τ-integrand produced by `integral_k_mul_weight` is integrable (Fubini). -/
theorem integrable_paperFT_mul_weightFT {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) {E : ℝ → ℂ}
    (hE : Integrable E) :
    Integrable (fun τ : ℝ => paperFT k τ * ∫ u : ℝ, E u * cexp (-I * τ * u)) := by
  have := (integrable_inversion_kernel hFk hE).swap.integral_prod_left
  refine this.congr ?_
  filter_upwards with τ
  simp only [Function.comp, Function.uncurry, Prod.swap]
  rw [← cintegral_const_mul]
  congr 1; ext u; ring





theorem integrable_exp_neg_abs_half :
    Integrable (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ)) := by
  simpa using integrable_exp_neg_abs_half_mul 0



theorem integrable_EL (L : ℝ) : Integrable (EL L) := by
  unfold EL
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
  exact (by fun_prop : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ)).continuousOn.integrableOn_compact
    isCompact_Icc




/-! ### Integrability of the three densities against h (from the computations above) -/





/-! ## Adding up -/


/-! ## [prop:EF] from the literature form -/


end EF
end Zeta23
end
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction
set_option backward.isDefEq.respectTransparency false
open Zeta23
open EF

theorem solution {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (𝓕 k)) :
    paperFT k (I / 2) + paperFT k (-I / 2)
      = ∫ τ : ℝ, paperFT k τ * (PiX (Real.exp L) τ : ℂ) := by
  have hkc : HasCompactSupport k := hasCompactSupport_of_tsupport_subset hks
  have hki : Integrable k := hk.integrable_of_hasCompactSupport hkc
  have hA_int : Integrable (fun u : ℝ => k u * (Real.exp (-|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB_int : Integrable (fun u : ℝ => k u * (Real.exp (|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI1 : Integrable (fun u : ℝ => k u * cexp (I * (I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI2 : Integrable (fun u : ℝ => k u * cexp (I * (-I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  -- Step 1: h(i/2) + h(−i/2) = ∫ k(u)(e^{−u/2} + e^{u/2}) du = ∫ k e^{−|u|/2} + ∫ k e^{|u|/2}
  have step1 : paperFT k (I / 2) + paperFT k (-I / 2)
      = (∫ u : ℝ, k u * (Real.exp (-|u| / 2) : ℂ)) + ∫ u : ℝ, k u * (Real.exp (|u| / 2) : ℂ) := by
    rw [← integral_add hA_int hB_int]
    unfold paperFT
    rw [← integral_add hI1 hI2]
    congr 1; ext u
    rw [← mul_add, ← mul_add]
    congr 1
    have ha : I * (I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hb : I * (-I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [ha, hb, ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_add,
      ← Complex.ofReal_add]
    congr 1
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu, neg_div]
    · rw [abs_of_nonpos hu, neg_neg, add_comm, neg_div]
  -- Step 2 (decaying half): ∫ k e^{−|u|/2} = (1/2π) ∫ h(τ) (1/4+τ²)^{-1} dτ
  have stepA : ∫ u : ℝ, k u * (Real.exp (-|u| / 2) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ * (1 / ((1 / 4 : ℂ) + τ ^ 2)) := by
    rw [integral_k_mul_weight hk hki hFk integrable_exp_neg_abs_half]
    simp_rw [integral_exp_neg_abs_half]
  -- Step 2 (growing half, truncated by supp k ⊆ [−L,L]): ∫ k e^{|u|/2} = (1/2π) ∫ h(τ) 2Re((X^s−1)/s) dτ
  have hkEL : (fun u : ℝ => k u * (Real.exp (|u| / 2) : ℂ)) = fun u => k u * EL L u := by
    ext u
    by_cases hu : u ∈ Icc (-L) L
    · simp [EL, hu]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hks h)), zero_mul, zero_mul]
  have stepB : ∫ u : ℝ, k u * (Real.exp (|u| / 2) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ *
          ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ) := by
    rw [hkEL, integral_k_mul_weight hk hki hFk (integrable_EL L)]
    simp_rw [integral_EL_mul _ hL]
  -- integrability of the two τ-integrands (from Fubini)
  have hintA : Integrable (fun τ : ℝ => paperFT k τ * (1 / ((1 / 4 : ℂ) + τ ^ 2))) := by
    have := integrable_paperFT_mul_weightFT hFk integrable_exp_neg_abs_half
    simp_rw [integral_exp_neg_abs_half] at this
    exact this
  have hintB : Integrable (fun τ : ℝ => paperFT k τ *
      ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ)) := by
    have := integrable_paperFT_mul_weightFT hFk (integrable_EL L)
    simp_rw [integral_EL_mul _ hL] at this
    exact this
  -- assemble Π_X
  rw [step1, stepA, stepB, ← mul_add, ← integral_add hintA hintB, ← cintegral_const_mul]
  congr 1; ext τ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 : (1 / 4 : ℂ) + τ ^ 2 ≠ 0 := by
    rw [show (1 / 4 : ℂ) + τ ^ 2 = ((1 / 4 + τ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by positivity : (1 / 4 + τ ^ 2 : ℝ) ≠ 0)
  simp only [PiX]
  push_cast
  field_simp
