-- Prove2me | solution 1 for Zeta23.EF.integrable_paperFT_mul_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:58:39.249122+00:00
-- url     : https://prove2.me/submissions/3a88197a-7aff-4465-a8db-1fcbd9c13dca

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_Hypotheses
import Theorems.Thm_Zeta23_EF_abs_mu_le_of_gammaFacts
import Theorems.Thm_Zeta23_EF_norm_fourier_mul_one_add_sq_le
import Theorems.Thm_Zeta23_norm_paperFT_le
import Theorems.Thm_Zeta23_norm_paperFT_mul_sq_le

-- from Zeta23.ExplicitFormula
section
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








/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/
















/-! ### Integrability of the three densities against h (from the computations above) -/





/-! ## Adding up -/


/-! ## [prop:EF] from the literature form -/


end EF
end Zeta23
end
end

-- from Zeta23.Poisson.PaperFT
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/


/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/





/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/






theorem hasCompactSupport_of_support_subset_abs {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -Λ) (b := Λ)) ?_
  intro u hu
  exact abs_le.mp (hsupp u hu)




end Zeta23
end

-- from Zeta23.ExplicitFormula.Bridge
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula/Bridge.lean

The two "all integrals absolutely convergent" side-facts of App. A [app:EF]:
  * `integrable_fourier_of_contDiff_two` : k ∈ C_c²(ℝ) ⇒ 𝓕 k ∈ L¹(ℝ)   (from [eq:hfbound], Zeta23/Poisson/PaperFT.lean);
  * `integrable_paperFT_mul_mu`          : k ∈ C_c²(ℝ) ⇒ h_k · μ ∈ L¹(ℝ)  (from [eq:hfbound] + H-Γ [eq:mufacts]);
and the clean bridge
  * `explicitFormulaPaper_of_lit` : EF_lit Z → GammaFacts → ExplicitFormulaPaper Z,
i.e. the literature-form explicit formula [eq:EFstd] (plus the Stirling facts for μ that PaperInputs already
carries) implies the paper's [prop:EF]/[eq:EF] exactly as Hypotheses.lean states it.
-/

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-- A compactly supported function on ℝ is supported in some `[−Λ, Λ]`. -/
theorem exists_abs_le_of_hasCompactSupport {k : ℝ → ℂ} (hkc : HasCompactSupport k) :
    ∃ Λ : ℝ, ∀ u, k u ≠ 0 → |u| ≤ Λ := by
  obtain ⟨R, hR⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => ?_⟩
  have := hR (subset_tsupport _ (Function.mem_support.mpr hu))
  simpa [Real.norm_eq_abs] using this


theorem continuous_fourier_of_integrable {k : ℝ → ℂ} (hki : Integrable k) : Continuous (𝓕 k) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner) hki

/-- `k ∈ C_c²(ℝ)` ⇒ `𝓕 k` integrable (App. A: "h(r) ≪_k (1+|r|)^{-2}"). -/
theorem integrable_fourier_of_contDiff_two {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) : Integrable (𝓕 k) := by
  obtain ⟨Λ, hΛ⟩ := exists_abs_le_of_hasCompactSupport hkc
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  set K : ℝ := (∫ u, ‖k u‖) + (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2)
  refine ((integrable_inv_one_add_sq.const_mul K).mono'
    (continuous_fourier_of_integrable hki).aestronglyMeasurable (Eventually.of_forall fun w => ?_))
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact norm_fourier_mul_one_add_sq_le hk hΛ w

/-- [eq:hfbound] on the real line for the paper transform: `‖h_k(τ)‖(1+τ²) ≤ ‖k‖₁ + ‖k''‖₁`. -/
theorem norm_paperFT_mul_one_add_sq_le {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) {Λ : ℝ}
    (hΛ : ∀ u, k u ≠ 0 → |u| ≤ Λ) (τ : ℝ) :
    ‖paperFT k τ‖ * (1 + τ ^ 2) ≤ (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ := by
  have hkc : HasCompactSupport k := Zeta23.hasCompactSupport_of_support_subset_abs hΛ
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have h1 := Zeta23.norm_paperFT_le hki hΛ (τ : ℂ)
  have h2 := Zeta23.norm_paperFT_mul_sq_le hk hΛ (τ : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h1 h2
  calc ‖paperFT k τ‖ * (1 + τ ^ 2) = ‖paperFT k τ‖ + ‖paperFT k τ‖ * τ ^ 2 := by ring
    _ ≤ _ := add_le_add h1 h2




end EF
end Zeta23
end
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate
set_option backward.isDefEq.respectTransparency false
open Zeta23
open EF

theorem solution {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΓ : GammaFacts) : Integrable (fun τ : ℝ => paperFT k τ * (mu τ : ℂ)) := by
  obtain ⟨Λ, hΛ⟩ := exists_abs_le_of_hasCompactSupport hkc
  obtain ⟨K₂, hK₂, hmu⟩ := abs_mu_le_of_gammaFacts hΓ
  set K₁ : ℝ := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ with hK₁
  have hK₁nn : 0 ≤ K₁ := by positivity
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => paperFT k τ * (mu τ : ℂ)) :=
    (integrable_paperFT_ofReal (integrable_fourier_of_contDiff_two hk hkc)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp hΓ.smooth.continuous).aestronglyMeasurable
  have hdom : Integrable (fun τ : ℝ => 2 * K₁ * K₂ * (1 + ‖τ‖) ^ (-(3 / 2) : ℝ)) :=
    (integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)).const_mul _
  refine hdom.mono' hmeas (Eventually.of_forall fun τ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hb : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
  have h1 : ‖paperFT k τ‖ * (1 + τ ^ 2) ≤ K₁ := norm_paperFT_mul_one_add_sq_le hk hΛ τ
  have h2 : |mu τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := hmu τ
  have hsq : (1 + |τ|) ^ (2 : ℝ) ≤ 2 * (1 + τ ^ 2) := by
    rw [Real.rpow_two]; nlinarith [sq_abs τ, sq_nonneg (1 - |τ|)]
  -- (1+|τ|)^{1/2} ≤ 2(1+τ²)(1+|τ|)^{-3/2}
  have key : (1 + |τ|) ^ (1 / 2 : ℝ) ≤ 2 * (1 + τ ^ 2) * (1 + |τ|) ^ (-(3 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 2 + (-(3 / 2)) by norm_num, Real.rpow_add hb]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hb.le _)
  calc ‖paperFT k τ‖ * |mu τ|
      ≤ ‖paperFT k τ‖ * (K₂ * (1 + |τ|) ^ (1 / 2 : ℝ)) := by gcongr
    _ ≤ ‖paperFT k τ‖ * (K₂ * (2 * (1 + τ ^ 2) * (1 + |τ|) ^ (-(3 / 2) : ℝ))) := by gcongr
    _ = (‖paperFT k τ‖ * (1 + τ ^ 2)) * (2 * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ)) := by ring
    _ ≤ K₁ * (2 * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ)) := by
        gcongr
    _ = 2 * K₁ * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ) := by ring
