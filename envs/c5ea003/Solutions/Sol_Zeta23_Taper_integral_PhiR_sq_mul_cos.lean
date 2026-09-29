-- Prove2me | solution 1 for Zeta23.Taper.integral_PhiR_sq_mul_cos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:38:08.238806+00:00
-- url     : https://prove2.me/submissions/82933c36-a983-4b15-8e71-2cdef3f5d75d

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic
import Theorems.Thm_Zeta23_Taper_integrable_re_paperFT_sq_and
import Theorems.Thm_Zeta23_Taper_integral_mul_cos_of_paperFT_eq
import Theorems.Thm_Zeta23_Taper_ofReal_autocorr_eq_convolution
import Theorems.Thm_Zeta23_Taper_paperFT_autocorr
import Theorems.Thm_Zeta23_Taper_paperFT_neg_of_even
import Theorems.Thm_Zeta23_Taper_phiSqC_supp
import Theorems.Thm_Zeta23_Taper_phi_contDiff
import Theorems.Thm_Zeta23_Taper_phi_support_subset

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

theorem paperFT_def (f : ℝ → ℂ) (z : ℂ) : paperFT f z = ∫ u : ℝ, f u * cexp (I * z * u) := rfl

/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/





/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/










end Zeta23
end

-- from Zeta23.Taper.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Basic.lean.  Definitions of the test family
[subsec:family] for generic parameters (ϱ : ℝ → ℝ) (L w : ℝ), and the basic facts of the sentence
after [eq:phidef].  Bodies are literally those of Zeta23/Defs.lean so that
P.phi T = Taper.phi P.ϱ (P.L T) P.w etc. are rfl (bridges in Zeta23/Taper.lean).

Sub-file map (umbrella = Zeta23/Taper.lean):
  Basic   — defs, support/plateau/evenness/C³
  Norms   — [eq:phinorms], [eq:abdef], c_ϱ, C₁, smoothstep
  Strip   — [eq:hfbound] specialized to φ
  Decay   — [eq:gbounds], [eq:psidef], [eq:psiints]
  Fourier — φ̂, Φ real/even/continuous, [eq:PhigA] facts, Plancherel, [eq:Phi2FT]
  Zeta23/Taper.lean — umbrella + the consumer-facing `Params` layer
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23




namespace Taper

/-! ### Constants depending only on ϱ  [eq:phinorms] -/






/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)











/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}

theorem phi_even (u : ℝ) : phi ϱ L w (-u) = phi ϱ L w u := by
  simp [phi, abs_neg]






theorem phi_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (phi ϱ L w) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (phi_support_subset hϱ hw)



theorem phi_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phi ϱ L w) :=
  (phi_contDiff hϱ hw hwL).continuous


end Basic



end Taper

end Zeta23
end

-- from Zeta23.Taper.Fourier
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Fourier.lean  (Fourier-side facts about the taper).
Canonical text: the paper, §2.2 [subsec:family]:
  "Thus φ̂ and Φ are real, even, entire; φ̂(0) ≤ L, Φ(0) = aL; φ̂² = Â_φ and Φ² = ĝ on ℝ;
   ∫_ℝ Φ² = 2π g(0) = 2π bL; g and A_φ are even".
Conventions: generic parameters (ϱ : ℝ → ℝ) (L w : ℝ); paper's
side condition is 1 ≤ w ≤ L/8 [eq:wrange]; each lemma carries the minimal hypothesis it needs.
The decay needed for integrability is taken directly
from Zeta23/Poisson/PaperFT.lean (norm_paperFT_le, norm_paperFT_mul_sq_le).

MATHLIB INVENTORY, what this file leans on:
* dictionary  Zeta23.paperFT_ofReal_eq_fourier : paperFT f s = 𝓕 f (-s/(2π))  (PaperFT.lean);
* convolution theorem  Real.fourier_mul_convolution_eq  (Mathlib/Analysis/Fourier/Convolution.lean)
  for integrable + continuous f₁ f₂ : ℝ → ℂ, 𝓕 (f₁ ⋆[mul ℂ ℂ] f₂) = 𝓕 f₁ · 𝓕 f₂ — the paper's
  autocorrelation (v ⋆ v)(y) = ∫ v(u) v(u+y) du coincides with Mathlib's convolution for EVEN v;
* Fourier inversion  MeasureTheory.Integrable.fourierInv_fourier_eq  (Mathlib/Analysis/Fourier/
  Inversion.lean): f, 𝓕 f integrable, f continuous at v ⇒ 𝓕⁻ (𝓕 f) v = f v.  "Plancherel"
  ∫ φ̂² = 2π ∫ φ² is obtained as inversion of Â_φ = φ̂² at 0 (no L² theory needed);
* smoothness  Real.contDiff_fourier  (Mathlib/Analysis/Fourier/FourierTransformDeriv.lean);
* integrable_inv_one_add_sq  (dominating function (1+r²)⁻¹ for the decay |φ̂(r)| ≤ min(C₀, C₂/r²)).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate

namespace Zeta23

/-! ### ℂ-specialized restatements of RCLike-generic integral lemmas
(same workaround as `integral_const_mul_C` in PaperFT.lean: `rw` with the
RCLike-stated lemma can fail to unify the `NormedAddCommGroup ℂ` instance path). -/


theorem integral_conj_C (f : ℝ → ℂ) : ∫ x, conj (f x) = conj (∫ x, f x) := integral_conj


namespace Taper

/-! ## Generic facts about the paper-convention transform `h_v(z) = ∫ v(u) e^{izu} du` of a REAL
function `v`.  Everything in the [eq:PhigA] sentence is an instance of these with `v = φ` or `v = φ²`. -/

section Generic

variable {v : ℝ → ℝ}

/-- For real `v`: `conj h_v(z) = h_v(−conj z)`. -/
theorem conj_paperFT_ofReal (v : ℝ → ℝ) (z : ℂ) :
    conj (paperFT (fun u => (v u : ℂ)) z) = paperFT (fun u => (v u : ℂ)) (-conj z) := by
  rw [paperFT_def, paperFT_def, ← integral_conj_C]
  congr 1 with u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring


/-- For real even `v` and real `r`, `h_v(r)` is real. -/
theorem paperFT_ofReal_eq_re (hv : ∀ u, v (-u) = v u) (r : ℝ) :
    paperFT (fun u => (v u : ℂ)) r = ((paperFT (fun u => (v u : ℂ)) r).re : ℂ) := by
  refine (Complex.conj_eq_iff_re.mp ?_).symm
  rw [conj_paperFT_ofReal, Complex.conj_ofReal, paperFT_neg_of_even hv]





/-! ### The paper's autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] versus Mathlib's convolution -/



theorem autocorr_continuous_of_even (hv : ∀ u, v (-u) = v u) (hc : Continuous v)
    (hs : HasCompactSupport v) : Continuous (Params.autocorr v) := by
  have hsC : HasCompactSupport (fun u => (v u : ℂ)) := hs.comp_left Complex.ofReal_zero
  have hcC : Continuous (fun u => (v u : ℂ)) := Complex.continuous_ofReal.comp hc
  have : Continuous (fun y => (Params.autocorr v y : ℂ)) := by
    rw [ofReal_autocorr_eq_convolution hv]
    exact hsC.continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
      (hcC.locallyIntegrable) hcC
  simpa [Function.comp_def] using Complex.continuous_re.comp this

theorem autocorr_integrable_of_even (hv : ∀ u, v (-u) = v u) (hc : Continuous v)
    (hs : HasCompactSupport v) : Integrable (Params.autocorr v) := by
  have hsC : HasCompactSupport (fun u => (v u : ℂ)) := hs.comp_left Complex.ofReal_zero
  have hcC : Continuous (fun u => (v u : ℂ)) := Complex.continuous_ofReal.comp hc
  have hiC : Integrable (fun u => (v u : ℂ)) := hcC.integrable_of_hasCompactSupport hsC
  have : Integrable (fun y => (Params.autocorr v y : ℂ)) := by
    rw [ofReal_autocorr_eq_convolution hv]
    exact hiC.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hiC
  simpa using this.re


/-! ## Fourier inversion in the paper's convention, cosine form -/


end Generic

/-! ## "`φ̂` and `Φ` are real, even, entire; …" (facts stated after [eq:PhigA]) -/

section PhigA
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### auxiliary packaging of φ and φ² as inputs to the generic lemmas -/

theorem phi_sq_even (u : ℝ) : phi ϱ L w (-u) ^ 2 = phi ϱ L w u ^ 2 := by rw [phi_even]

theorem phi_sq_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (fun u => phi ϱ L w u ^ 2) :=
  (phi_hasCompactSupport hϱ hw).comp_left (g := fun x : ℝ => x ^ 2) (by simp)







theorem phiSqC_contDiff_two (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) := by
  have := Complex.ofRealCLM.contDiff.comp (((phi_contDiff hϱ hw hwL).pow 2).of_le (m := 2) (by norm_num))
  simpa [Function.comp_def] using this


/-! #### real / even / conjugation symmetry (hypothesis-free: only "φ real and even" is used) -/


theorem Phi_ofReal (r : ℝ) : Phi ϱ L w r = (PhiR ϱ L w r : ℂ) :=
  paperFT_ofReal_eq_re (v := fun u => phi ϱ L w u ^ 2) phi_sq_even r




/-! #### continuity / differentiability on ℝ ("entire" is more than any consumer needs) -/




/-! #### values at 0 -/






/-! #### "`φ̂² = Â_φ` and `Φ² = ĝ` on ℝ" — convolution theorem -/


/-- "`Φ² = ĝ` on ℝ". -/
theorem PhiR_sq_eq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    ((PhiR ϱ L w r) ^ 2 : ℂ) = paperFT (fun u => (g ϱ L w u : ℂ)) r := by
  have h := paperFT_autocorr (v := fun u => phi ϱ L w u ^ 2) phi_sq_even
    ((phi_continuous hϱ hw hwL).pow 2) (phi_sq_hasCompactSupport hϱ hw) r
  have h2 : paperFT (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) r = (PhiR ϱ L w r : ℂ) :=
    Phi_ofReal r
  beta_reduce at h
  rw [h2] at h
  exact h.symm

/-! #### integrability of `φ̂², φ̂²|r|, Φ², Φ²|r|` (decay [eq:hfbound] via PaperFT.lean) -/



theorem integrable_PhiR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun x => PhiR ϱ L w x ^ 2) :=
  (integrable_re_paperFT_sq_and (phiSqC_contDiff_two hϱ hw hwL) (phiSqC_supp hϱ hw)).1


/-! #### Plancherel / inversion identities -/





end PhigA

end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (y : ℝ) : ∫ x, PhiR ϱ L w x ^ 2 * Real.cos (x * y) = 2 * π * g ϱ L w y :=
  integral_mul_cos_of_paperFT_eq (A := g ϱ L w) (G := fun r => PhiR ϱ L w r ^ 2)
    (autocorr_continuous_of_even phi_sq_even ((phi_continuous hϱ hw hwL).pow 2)
      (phi_sq_hasCompactSupport hϱ hw))
    (autocorr_integrable_of_even phi_sq_even ((phi_continuous hϱ hw hwL).pow 2)
      (phi_sq_hasCompactSupport hϱ hw))
    (integrable_PhiR_sq hϱ hw hwL)
    (fun r => by rw [← PhiR_sq_eq hϱ hw hwL r]; push_cast; ring) y
