-- Prove2me | solution 1 for Zeta23.Taper.hasSum_phiHatR_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:50:27.966693+00:00
-- url     : https://prove2.me/submissions/1021fdad-a7d0-4a16-881e-424dc56df1c6

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic
import Theorems.Thm_Zeta23_Poisson_hasSum_paperFT_mul_paperFT
import Theorems.Thm_Zeta23_Taper_norm_phiHat_le
import Theorems.Thm_Zeta23_Taper_paperFT_neg_of_even
import Theorems.Thm_Zeta23_Taper_phi_contDiff
import Theorems.Thm_Zeta23_norm_paperFT_mul_sq_le

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



/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith






theorem phi_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phi ϱ L w) :=
  (phi_contDiff hϱ hw hwL).continuous


end Basic



end Taper

end Zeta23
end

-- from Zeta23.Taper.Strip
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Strip.lean.
[eq:hfbound] specialized to `f = φ`, `Λ_f = L/2` (as consumed by [prop:tail]):
"`|φ̂(r − iy)| ≤ e^{L/4} ‖φ''‖₁ |r − iy|⁻²`" for `|y| ≤ 1/2`.
All three statements are proved here from the general-`f` bounds in Zeta23/Poisson/PaperFT.lean,
and are consumed via `Zeta23.Params.norm_phiHat_*`.
Reference: the paper, §2.1 [eq:hfbound], §4 [prop:tail].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

section HfPhi
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- `u ↦ (φ u : ℂ)` is `C³`. -/
theorem phiC_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 3 (fun u => (phi ϱ L w u : ℂ)) :=
  ofRealCLM.contDiff.comp (phi_contDiff hϱ hw hwL)

theorem phiC_support (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (phi ϱ L w u : ℂ) ≠ 0 → |u| ≤ L / 2 := by
  intro u hu
  by_contra h
  exact hu (by rw [phi_eq_zero hϱ hw (le_of_lt (not_le.mp h)), ofReal_zero])

/-- `deriv` commutes with the coercion `ℝ → ℂ` for differentiable functions. -/
theorem deriv_ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (fun u => (f u : ℂ)) = fun u => ((deriv f u : ℝ) : ℂ) := by
  funext u
  exact ((hf u).hasDerivAt.ofReal_comp).deriv

theorem deriv_deriv_phiC (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    deriv (deriv (fun u => (phi ϱ L w u : ℂ)))
      = fun u => ((deriv (deriv (phi ϱ L w)) u : ℝ) : ℂ) := by
  have h3 := phi_contDiff hϱ hw hwL
  have hd1 : Differentiable ℝ (phi ϱ L w) := h3.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv (phi ϱ L w)) :=
    (h3.deriv' (n := 2)).differentiable (by norm_num)
  rw [deriv_ofReal_comp hd1, deriv_ofReal_comp hd2]

/-- [eq:hfbound] for φ: `‖φ̂(z)‖ · ‖z‖² ≤ e^{|Im z|·L/2} · C₁` for all complex `z`,
`C₁ = ‖φ''‖₁`. -/
theorem norm_phiHat_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (z : ℂ) :
    ‖phiHat ϱ L w z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * (L / 2)) * C1 ϱ L w := by
  have h := norm_paperFT_mul_sq_le ((phiC_contDiff hϱ hw hwL).of_le (by norm_num))
    (phiC_support hϱ hw) z
  rw [deriv_deriv_phiC hϱ hw hwL] at h
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  exact h




end HfPhi

end Taper

end Zeta23
end

-- from Zeta23.Taper.Fourier
section
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






/-! ## Fourier inversion in the paper's convention, cosine form -/


end Generic

/-! ## "`φ̂` and `Φ` are real, even, entire; …" (facts stated after [eq:PhigA]) -/

section PhigA
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### auxiliary packaging of φ and φ² as inputs to the generic lemmas -/

theorem phi_sq_even (u : ℝ) : phi ϱ L w (-u) ^ 2 = phi ϱ L w u ^ 2 := by rw [phi_even]










/-! #### real / even / conjugation symmetry (hypothesis-free: only "φ real and even" is used) -/

/-- `φ̂` real on ℝ: `φ̂(r) = ↑(Re φ̂(r))` for real `r` (φ even and real). -/
theorem phiHat_ofReal (r : ℝ) : phiHat ϱ L w r = (phiHatR ϱ L w r : ℂ) :=
  paperFT_ofReal_eq_re (v := phi ϱ L w) phi_even r

theorem Phi_ofReal (r : ℝ) : Phi ϱ L w r = (PhiR ϱ L w r : ℂ) :=
  paperFT_ofReal_eq_re (v := fun u => phi ϱ L w u ^ 2) phi_sq_even r




/-! #### continuity / differentiability on ℝ ("entire" is more than any consumer needs) -/




/-! #### values at 0 -/






/-! #### "`φ̂² = Â_φ` and `Φ² = ĝ` on ℝ" — convolution theorem -/



/-! #### integrability of `φ̂², φ̂²|r|, Φ², Φ²|r|` (decay [eq:hfbound] via PaperFT.lean) -/





/-! #### Plancherel / inversion identities -/





end PhigA

end Taper

end Zeta23
end

-- from Zeta23.Poisson
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
[lem:poisson] "Poisson summation for the Gabor system", the paper §2.2:

  "For all τ, τ' ∈ ℝ,
     K_∞(τ,τ') := Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L·Φ(τ−τ'),   in particular   Σ_{k∈ℤ} φ̂(τ−τ_k)² = aL²."

Here τ_k := T + k h, h := 2π/L [eq:fk], Φ := (φ²)^ [eq:PhigA], a := L⁻¹∫φ² [eq:abdef], and
φ̂(s) = ∫ φ(u) e^{isu} du is the paper's Fourier convention (`Zeta23.paperFT`).  Only the
real-argument identity is proved (that is all [prop:block](ii) uses; the complex continuation
mentioned in [rem:pairblock] is not used by the proof).

Proof route (the paper's, rearranged so that Fourier inversion is not needed): with
  G(ξ) := L · ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du      (= L e^{−iTLξ}(φ_τ ∗ φ_{τ'})(Lξ)),
G is continuous with support in [−1,1] and G(k) = 0 for k ∈ ℤ∖{0} (because φ(u) = 0 for
|u| ≥ L/2), G(0) = L ∫ φ(u)φ(−u)e^{i(τ−τ')u} du = L Φ(τ−τ') (φ even), and a Fubini computation
gives 𝓕G(w) = φ̂(τ−τ_w) φ̂(τ'−τ_w) for Mathlib's 𝓕 and every real w (τ_w := T + w·2π/L).
Mathlib's Poisson summation `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`
(Σ_k G(k) = Σ_n 𝓕G(n)) then gives the claim; summability of n ↦ φ̂(τ−τ_n)φ̂(τ'−τ_n) comes from
the decay |φ̂(r)| ≪ (1+r²)⁻¹, i.e. [eq:hfbound]/[eq:psidef].
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace Zeta23

namespace Poisson

/-! #### A decay-to-`IsBigO` lemma -/


/-! #### The auxiliary function `G` -/

variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)



variable {φ L T τ τ'}










/-! #### The abstract identity -/


end Poisson

namespace Taper

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- Decay input for Poisson: `|φ̂(s)|(1 + s²) ≤ L + C₁` on ℝ (from [eq:hfbound] at `y = 0`). -/
theorem phiHat_decay (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (phi ϱ L w u : ℂ)) s‖ * (1 + s ^ 2) ≤ C := by
  refine ⟨L + C1 ϱ L w, fun s => ?_⟩
  have h0 := norm_phiHat_le hϱ hw hwL s
  have h2 := norm_phiHat_mul_sq_le hϱ hw hwL s
  simp only [ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, norm_real,
    Real.norm_eq_abs, sq_abs] at h0 h2
  unfold phiHat at h0 h2
  linarith



end Taper

namespace Params

variable {P : Params} {T : ℝ}


variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL




end Params

end Zeta23
open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => phiHatR ϱ L w (τ - (T + k * (2 * π / L)))
                          * phiHatR ϱ L w (τ' - (T + k * (2 * π / L))))
      (L * PhiR ϱ L w (τ - τ')) := by
  have hL : 0 < L := by linarith
  have h := Poisson.hasSum_paperFT_mul_paperFT hL (phi_continuous hϱ hw hwL)
    (fun u hu => phi_eq_zero hϱ hw hu) (fun u => phi_even u) (phiHat_decay hϱ hw hwL) T τ τ'
  -- transport along re : ℂ → ℝ
  have h2 := (Complex.reCLM.hasSum h)
  convert h2 using 1
  · funext k
    simp only [Complex.reCLM_apply]
    rw [show paperFT (fun u => (phi ϱ L w u : ℂ)) = phiHat ϱ L w from rfl,
      phiHat_ofReal, phiHat_ofReal]
    norm_cast
  · simp only [Complex.reCLM_apply]
    rw [show paperFT (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) = Phi ϱ L w from rfl, Phi_ofReal]
    norm_cast
