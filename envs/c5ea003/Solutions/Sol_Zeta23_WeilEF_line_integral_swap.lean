-- Prove2me | solution 1 for Zeta23.WeilEF.line_integral_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:15:11.838807+00:00
-- url     : https://prove2.me/submissions/c70cd9be-dfd2-4fa0-8e7c-d1100a1e62dd

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Theorems.Thm_Zeta23_EF_norm_fourier_mul_one_add_sq_le

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

-- from Zeta23.ExplicitFormula.Bridge
section
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





end EF
end Zeta23
end
end

-- from Zeta23.WeilEF.VerticalLine
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/VerticalLine.lean.  Vertical-line integrals for the EF contour.

KEY DEVICE (no contour shifting needed on the prime side): for s = c + it on a vertical line,
H(s) := h((s−1/2)/i) = paperFT k (t − i·b) with b := c − 1/2, and
  paperFT k (t − i·b) = paperFT k_b t,  where k_b(u) := k(u)·e^{b·u}  (the TILTED test function,
still C_c²).  Hence the line integral (1/2π)∫ H(c+it)·n^{−c−it} dt is, by Fourier inversion of
k_b (Zeta23.EF.paper_inversion, proved in Zeta23/ExplicitFormula.lean, with integrability from
Zeta23/ExplicitFormula/Bridge.lean's integrable_fourier_of_contDiff_two),
  n^{−c}·k_b(log n) = n^{−c}·k(log n)·n^{b} = n^{−1/2}·k(log n).
Summing against −ζ'/ζ(c+it) = Σ Λ(n)n^{−c−it} (Mathlib LSeries, 1 < c) with a dominated
tsum/integral swap (domination: ‖paperFT k_b t‖(1+t²) ≤ ‖k_b‖₁+‖k_b''‖₁ from
Zeta23.EF.norm_paperFT_mul_one_add_sq_le × Σ Λ(n)n^{−c} < ∞) gives the prime side.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex MeasureTheory
open scoped ArithmeticFunction



theorem tilt_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (b : ℝ) : ContDiff ℝ 2 (tilt k b) := by
  refine hk.mul ?_
  have : ContDiff ℝ 2 (fun u : ℝ => Real.exp (b * u)) := (Real.contDiff_exp.comp
    (contDiff_const.mul contDiff_id)).of_le le_top
  exact Complex.ofRealCLM.contDiff.comp this

theorem tilt_hasCompactSupport {k : ℝ → ℂ} (hk : HasCompactSupport k) (b : ℝ) :
    HasCompactSupport (tilt k b) := by
  refine hk.mul_right

















end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    ∫ t : ℝ, (∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n)
      = ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
  have hkb2 : ContDiff ℝ 2 (tilt k (c - 1/2)) := tilt_contDiff hk _
  have hkbc : HasCompactSupport (tilt k (c - 1/2)) := tilt_hasCompactSupport hkc _
  have hFkb := Zeta23.EF.integrable_fourier_of_contDiff_two hkb2 hkbc
  have hpfi : Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t) :=
    Zeta23.EF.integrable_paperFT_ofReal hFkb
  have hre : ∀ t : ℝ, ((c:ℂ) + t * I).re = c := by
    intro t
    simp
  have hnorm : ∀ (n : ℕ) (t : ℝ), ‖LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖
      = if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)) := by
    intro n t
    rw [LSeries.norm_term_eq, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]
  have hcont : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun t => ?_)
      · refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
        exact_mod_cast hn
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n) := by
    intro n
    refine hpfi.mul_bdd (c := if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)))
      (hcont n).aestronglyMeasurable ?_
    filter_upwards with t
    rw [hnorm n t]
  have heval : ∀ n : ℕ, (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖)
      = (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)
        * (if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
    intro n
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [norm_mul, hnorm n t]
  have hcn : Summable (fun n : ℕ => if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
    have hs : LSeriesSummable (fun n => (Λ n : ℂ)) (c : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc1)
    have hns : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖) :=
      summable_norm_iff.mpr hs
    refine hns.congr fun n => ?_
    simpa using hnorm n 0
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖) := by
    refine ((hcn.mul_left (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)).congr fun n => ?_)
    rw [heval n]
  exact (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq.symm
