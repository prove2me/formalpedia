-- Prove2me | solution 1 for Zeta23.EF.k_add_k_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:52:37.960785+00:00
-- url     : https://prove2.me/submissions/dc6dc626-8c26-49c1-9be4-47f4137950ce

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



/-! ## Dictionary with Mathlib's Fourier transform -/

/-- `h_k(τ) = 𝓕 k (−τ/(2π))` for real τ. -/
theorem paperFT_ofReal_eq_fourier (k : ℝ → ℂ) (τ : ℝ) :
    paperFT k τ = 𝓕 k (-τ / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold paperFT
  congr 1; ext u
  rw [smul_eq_mul, mul_comm (k u)]
  congr 1
  have : (-2 * π * u * (-τ / (2 * π))) = τ * u := by
    field_simp
  rw [this]
  push_cast
  ring_nf

/-- `h_k` is integrable on the real line when `𝓕 k` is (dictionary + linear substitution). -/
theorem integrable_paperFT_ofReal {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ) := by
  have : (fun τ : ℝ => paperFT k τ) = fun τ => (𝓕 k) ((-(1 / (2 * π))) * τ) := by
    ext τ; rw [paperFT_ofReal_eq_fourier, show -(1 / (2 * π)) * τ = -τ / (2 * π) by ring]
  rw [this]
  exact hFk.comp_mul_left' (neg_ne_zero.mpr (by positivity))


/-! ## The test function k = f ⋆ g̃ -/










/-! ## App. A: the three identifications -/



/-- `h(r) e^{-irw}` is integrable in r when h is. -/
theorem integrable_paperFT_mul_cexp {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) (w : ℝ) :
    Integrable (fun r : ℝ => paperFT k r * cexp (-I * r * w)) := by
  refine (integrable_paperFT_ofReal hFk).mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with r
  rw [Complex.norm_exp]
  simp





/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/
















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

theorem solution {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (y : ℝ) :
    k y + k (-y) = (1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ * (Real.cos (τ * y) : ℂ) := by
  rw [paper_inversion hk hki hFk y, paper_inversion hk hki hFk (-y), ← mul_add,
    ← integral_add (integrable_paperFT_mul_cexp hFk y) (integrable_paperFT_mul_cexp hFk (-y))]
  have h2 : ∀ τ : ℝ, paperFT k τ * cexp (-I * τ * y) + paperFT k τ * cexp (-I * τ * ↑(-y))
      = 2 * (paperFT k τ * (Real.cos (τ * y) : ℂ)) := by
    intro τ
    rw [← mul_add, Complex.ofReal_cos, mul_left_comm, Complex.two_cos, add_comm]
    congr 2
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  simp_rw [h2]
  rw [cintegral_const_mul, ← mul_assoc]
  congr 1
  field_simp
