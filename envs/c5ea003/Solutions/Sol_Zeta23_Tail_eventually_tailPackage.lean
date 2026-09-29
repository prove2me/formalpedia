-- Prove2me | solution 1 for Zeta23.Tail.eventually_tailPackage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:48:54.622062+00:00
-- url     : https://prove2.me/submissions/9cb6e103-8e23-4077-adec-1e51516297a2

import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_Taper_Basic
import Definitions.Def_Zeta23_Taper_Params
import Theorems.Thm_Zeta23_GzGp_phiHat_conj
import Theorems.Thm_Zeta23_Tail_eventually_tailInputs
import Theorems.Thm_Zeta23_Tail_theta0_le
import Theorems.Thm_Zeta23_Taper_bConst_le_aConst
import Theorems.Thm_Zeta23_Taper_integral_abs_deriv2_phi
import Theorems.Thm_Zeta23_Taper_one_sub_le_bConst
import Theorems.Thm_Zeta23_Taper_phi_contDiff
import Theorems.Thm_Zeta23_norm_paperFT_mul_sq_le

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




/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith








end Basic



end Taper

end Zeta23
end

-- from Zeta23.Taper.Norms
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper


/-! ### [eq:phinorms] -/

section Norms
variable {ϱ : ℝ → ℝ} {L w : ℝ}
















lemma l1Deriv2_nonneg (ϱ : ℝ → ℝ) : 0 ≤ l1Deriv2 ϱ :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _












theorem C1_eq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    C1 ϱ L w = 2 * l1Deriv2 ϱ / w := integral_abs_deriv2_phi hϱ hw hwL

/-- "Finally `C₁ ≤ 2‖ϱ''‖₁` as `w ≥ 1`" [prop:tail proof, last lines]. -/
theorem C1_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) :
    C1 ϱ L w ≤ 2 * l1Deriv2 ϱ := by
  rw [C1_eq hϱ (by linarith) hwL]
  have := l1Deriv2_nonneg ϱ
  exact div_le_self (by linarith) hw

end Norms

/-! ### [eq:abdef]: "`1 − 2w/L ≤ b ≤ a ≤ 1`" -/

section AB
variable {ϱ : ℝ → ℝ} {L w : ℝ}







end AB


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



/-- The form used in [prop:tail]: for real `r` and `|y| ≤ 1/2`, `z := r − iy ≠ 0`,
`‖φ̂(r − iy)‖ ≤ e^{L/4} C₁ / ‖r − iy‖²`. -/
theorem norm_phiHat_sub_I_mul_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖phiHat ϱ L w (r - I * y)‖ ≤ Real.exp (L / 4) * C1 ϱ L w / ‖(r : ℂ) - I * y‖ ^ 2 := by
  have hL : 0 ≤ L := by linarith
  have hC1 : 0 ≤ C1 ϱ L w := integral_nonneg (fun _ => abs_nonneg _)
  rw [le_div_iff₀ (by positivity)]
  refine le_trans (norm_phiHat_mul_sq_le hϱ hw hwL _) ?_
  gcongr
  have him : ((r : ℂ) - I * y).im = -y := by simp
  rw [him, abs_neg]
  nlinarith

end HfPhi

end Taper

end Zeta23
end

-- from Zeta23.Taper.Params
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Params.lean.  Consumer-facing layer, part 1:
the `P : Params`, `T : ℝ` versions of everything that depends only on Taper/Basic, Taper/Norms
and Taper/Strip (φ facts [eq:phidef], [eq:abdef], C₁ and [eq:hfbound] for φ), plus the rfl
bridges to Defs.  Split out of Zeta23/Taper.lean so that Zeta23/Main.lean can import it without
pulling Taper/Decay, Taper/Fourier.  Hypotheses: `hP : P.Valid`,
`hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).  The remaining Params-layer facts (φ̂/Φ, ψ, g, A_φ,
Plancherel) are in the umbrella Zeta23/Taper.lean.
-/

open Complex MeasureTheory Real Set Filter Topology

namespace Zeta23

namespace Params

variable (P : Params) (T : ℝ)





variable {P T}

theorem w_pos (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
theorem two_w_le (hwL : 8 * P.w ≤ P.L T) (hP : P.Valid) : 2 * P.w ≤ P.L T := by
  linarith [hP.one_le_w]

/-! #### hypothesis-free facts -/

section
variable (hP : P.Valid)
include hP
end

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ -/

/-! #### [eq:abdef] -/
theorem b_le_a : P.b T ≤ P.a T := Taper.bConst_le_aConst hP.taper (w_pos hP) (two_w_le hwL hP)
theorem one_sub_le_b : 1 - 2 * P.w / P.L T ≤ P.b T :=
  Taper.one_sub_le_bConst hP.taper (w_pos hP) (two_w_le hwL hP)
theorem three_quarters_le_b : 3 / 4 ≤ P.b T := by
  have h1 := one_sub_le_b hP hwL
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have : 2 * P.w / P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]; linarith
  linarith
/-- "and `a ≥ 1/2`" [prop:tail, last line]. -/
theorem half_le_a : 1 / 2 ≤ P.a T := by
  linarith [three_quarters_le_b hP hwL, b_le_a hP hwL]

/-! #### [eq:hfbound] for φ ([prop:tail]) -/
theorem C1_le : P.C1 T ≤ 2 * Taper.l1Deriv2 P.ϱ :=
  Taper.C1_le hP.taper hP.one_le_w (two_w_le hwL hP)
theorem norm_phiHat_sub_I_mul_le (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * P.C1 T / ‖(r : ℂ) - I * y‖ ^ 2 :=
  Taper.norm_phiHat_sub_I_mul_le hP.taper (w_pos hP) (two_w_le hwL hP) r y hy hz

end

end Params

end Zeta23
end

-- from Zeta23.Tail
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail.lean — Proposition [prop:tail] (the paper §4.2 "The tail"), assembled for the
concrete objects of Zeta23/Defs.lean.

Paper, verbatim: "Proposition [prop:tail]. Let A₀ ≥ 1 be an absolute constant such that
N(t+1)−N(t) ≤ A₀ log(t+3) for all t ≥ 0. Then for T ≥ T₀,
  ‖Ẽ‖ ≤ θ₀ := 4A₀ C₁² X^{1/2} log(4T)/D₀²,   C₁ := ‖φ″‖₁ = 2‖ϱ″‖₁/w,
so that θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1} ≪ l T^{λ/2−1}. Moreover the trace norm satisfies
‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L."
Here E := G − A [eq:AE] is the contribution of the zeros with ordinate γ ∉ I' := (T−D₀, 2T+D₀],
D₀ := T^{1/2} [eq:D0] (including all zeros with γ ≤ 0), Ẽ := E/L,
Ê := E/(aL²) [eq:hatunits].

Structure of the proof (sub-files):
* Zeta23/Tail/RankOne.lean — ‖E‖, ‖E‖₁ ≤ ∑ m_ρ ‖u_ρ‖₂² for E = ∑ m_ρ u_ρ u_ρᵀ  [eq:Enormsum];
* Zeta23/Tail/Grid.lean    — ∑_{k<d} |γ−τ_k|⁻⁴ ≤ L·dist(γ,I)⁻³;
* Zeta23/Tail/Count.lean   — ∑_{γ∉I'} m_ρ dist(γ,I)⁻³ ≤ 4A₀ log(4T)/T, and N(I'∖I) ≪ D₀ l;
* this file              — [eq:hfbound] ⇒ ‖u_ρ k‖ ≤ e^{L/4}C₁|γ−τ_k|⁻², summability of the
  zero-side series entrywise, E = (the series over γ ∉ I'), and the two bounds in the exact
  shapes consumed downstream: ∀ i, |λᵢ(Ẽ)| ≤ θ₀ (for RHLinalg.weyl_posIndexAbove_le) and
  traceNorm Ê ≤ θ₀/(aL) (for [prop:zeroside-rank]).

Hypotheses taken (all proved elsewhere in the repository; none are Lean axioms):
* hloc  — PaperInputs.RvM.local (Hypotheses.lean), two-sided unit-window form;
* hdecay — [eq:hfbound] specialised to f = φ, in the exact shape of
  Zeta23.Params.norm_phiHat_sub_I_mul_le (Taper.lean), with C₁ := P.C1 T = ‖φ″‖₁;
* hEt/hEh — Hermitian-ness of Ẽ, Ê (from the ρ ↦ 1−ρ̄ symmetry).
-/

noncomputable section

open Matrix Finset Complex
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

/-! ### θ₀ and its size -/





/-! ### The local count from PaperInputs.RvM.local -/


/-! ### The vectors u_ρ and their decay from [eq:hfbound] -/

section Concrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)




variable {P T}




variable {Z}



end Concrete

/-! ### Summability of the zero-side series and E as the series over γ ∉ I' -/

section Series

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}



namespace TailHyp

variable (H : TailHyp Z P T A₀ C₁)
include H













end TailHyp

/-! ### Proposition [prop:tail] -/


end Series

/-! ### E is Hermitian (real symmetric) — "since ρ and 1−ρ̄ have the same ordinate, both index
sets are invariant under ρ ↦ 1−ρ̄, so A and E are real symmetric" [eq:AE] -/

section Hermitian




variable {P : Params} {T : ℝ}


variable {Z : ZeroConfig} {A₀ C₁ : ℝ}





end Hermitian

/-! ### Exports in the shapes consumed by Zeta23/Assembly.lean (Assembly.TailInputs) -/

section Export

open Filter

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}



/-- L = λ log(T/2π) → ∞; in particular eventually L ≥ 2 (and ≥ 8w, etc.). -/
lemma tendsto_L_atTop (P : Params) (hP : P.Valid) : Tendsto (fun T => P.L T) atTop atTop := by
  unfold Params.L l
  apply Tendsto.const_mul_atTop hP.lam_pos
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))


/-- **The "so that" clause, eventually**: if C₁(T) ≤ 2R (R = ‖ϱ″‖₁; Taper's C1_le with w ≥ 1),
then θ₀(T) ≤ 32A₀R² · l(T) · T^{λ/2−1} for T ≥ T₀; hence ∃ C, eventually θ₀ ≤ C·l·T^{λ/2−1}. -/
theorem eventually_theta0_le (P : Params) (hP : P.Valid) {A₀ R : ℝ} (hA₀ : 1 ≤ A₀)
    (C₁ : ℝ → ℝ) (hC₁ : ∀ T, 0 ≤ C₁ T) (hC₁R : ∀ᶠ T in atTop, C₁ T ≤ 2 * R) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      theta0 A₀ (Real.exp (P.L T / 4) * C₁ T) T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  refine ⟨32 * A₀ * R ^ 2, ?_⟩
  filter_upwards [eventually_ge_atTop T₀, hC₁R] with T hT hR
  exact theta0_le P hP hT (by linarith) (hC₁ T) hR


end Export

end Tail
end Zeta23
end
end

-- from Zeta23.Tail.Package
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Package.lean — [prop:tail] with all its analytic inputs discharged from the
repository's other files, in the exact shape Zeta23/Main.lean consumes ("hTailPkg").

Inputs discharged here: A₀ and the local count from PaperInputs.RvM.local_count
(Hypotheses.lean); [eq:hfbound] for φ = Zeta23.Params.norm_phiHat_sub_I_mul_le, a ≥ 1/2 =
Zeta23.Params.half_le_a, C₁ ≤ 2‖ϱ″‖₁ = Zeta23.Params.C1_le (Taper.lean);
conj φ̂(z̄) = φ̂(z) = Zeta23.GzGp.phiHat_conj (hypothesis-free). The side condition 8w ≤ L
[eq:wrange] holds eventually since L = λ log(T/2π) → ∞ (Zeta23.Tail.tendsto_L_atTop).
-/

noncomputable section

open Filter Complex

namespace Zeta23
namespace Tail

/-- C₁ = ‖φ″‖₁ ≥ 0. -/
lemma C1_nonneg (P : Params) (T : ℝ) : 0 ≤ P.C1 T :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _


end Tail
end Zeta23
end
open Filter Complex
open Zeta23
open Tail

theorem solution (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z P T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := (tendsto_L_atTop P hP).eventually_ge_atTop _
  refine ⟨fun T => theta0 A₀ (Real.exp (P.L T / 4) * P.C1 T) T, ?_, ?_⟩
  · refine eventually_tailInputs Z P hP hA₀ hloc (fun T => P.C1 T) (fun T => C1_nonneg P T)
      ?_ ?_ ?_
    · filter_upwards [hwL] with T hwL
      exact fun r y hy hz => Params.norm_phiHat_sub_I_mul_le hP hwL r y hy hz
    · filter_upwards [hwL] with T hwL
      linarith [Params.half_le_a hP hwL]
    · exact Eventually.of_forall fun T z => GzGp.phiHat_conj P T z
  · exact eventually_theta0_le P hP hA₀ (fun T => P.C1 T) (fun T => C1_nonneg P T)
      (hwL.mono fun T hwL => Params.C1_le hP hwL)
