-- Prove2me | solution 1 for Zeta23.PrimeSide.nu_grid_bound_raw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:59:49.202118+00:00
-- url     : https://prove2.me/submissions/11571f07-7361-411f-9276-d9196c33d6bb

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Theorems.Thm_Zeta23_PrimeSide_Mnear_integrableOn
import Theorems.Thm_Zeta23_PrimeSide_dom_left
import Theorems.Thm_Zeta23_PrimeSide_dom_right
import Theorems.Thm_Zeta23_PrimeSide_integrableOn_sigma_mul_abs_nuX
import Theorems.Thm_Zeta23_PrimeSide_integral_Mfar_le
import Theorems.Thm_Zeta23_PrimeSide_integral_Mnear_le
import Theorems.Thm_Zeta23_PrimeSide_setIntegral_Iio_comp_sub_left
import Theorems.Thm_Zeta23_PrimeSide_setIntegral_Ioi_comp_sub_right

-- from Zeta23.PrimeSideA.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/


-- Contains: LocalHyps, EventuallyAt, the 𝓜-bilinearity/sup-bound lemmas, the large-T regime
-- lemmas, and all per-grid-point lemmas for [prop:trace].

/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Hypothesis packages

H-Γ and H-cheb are Zeta23/Hypotheses.lean's `Zeta23.GammaFacts` and `Zeta23.ChebyshevMertens` (about the
concrete `Zeta23.mu` and Λ-sums), taken verbatim.  The taper/test-family facts are packaged here: -/




/-! ### Bilinearity and symmetry of 𝓜[·,·] (§5.4: "a symmetric bilinear form (Φ² is even)") -/

section MformLemmas
variable {Φ : ℝ → ℝ} {T : ℝ}








end MformLemmas


/-! ### The "insert sup bounds" estimate for 𝓜[·,·]  (§5.4) -/

section SupBound
variable {Φ : ℝ → ℝ} {T : ℝ}



end SupBound


/-! ### The large-T regime: elementary consequences of the hypotheses -/

section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


/-- `l ≥ l₀` once `T ≥ 2π e^{l₀}`. -/
lemma Setting.le_l_of_T {p : Setting} {l₀ : ℝ} (hT : 2 * π * Real.exp l₀ ≤ p.T) : l₀ ≤ p.l := by
  have h2π : (0:ℝ) < 2 * π := by positivity
  have h : Real.exp l₀ ≤ p.T / (2 * π) := by rw [le_div_iff₀ h2π]; linarith
  calc l₀ = Real.log (Real.exp l₀) := (Real.log_exp _).symm
    _ ≤ Real.log (p.T / (2 * π)) := Real.log_le_log (Real.exp_pos _) h
    _ = p.l := rfl

/-- `T ≥ 2π` (in particular `T ≥ 1`, `T > 0`) once `T ≥ 2π e^{l₀}` with `l₀ ≥ 0`. -/
lemma Setting.twopi_le_T {p : Setting} {l₀ : ℝ} (hl₀ : 0 ≤ l₀) (hT : 2 * π * Real.exp l₀ ≤ p.T) :
    2 * π ≤ p.T := by
  have : (1:ℝ) ≤ Real.exp l₀ := Real.one_le_exp hl₀
  nlinarith [Real.pi_pos]

lemma Setting.one_le_T {p : Setting} {l₀ : ℝ} (hl₀ : 0 ≤ l₀) (hT : 2 * π * Real.exp l₀ ≤ p.T) :
    1 ≤ p.T := by
  have := Setting.twopi_le_T hl₀ hT; linarith [Real.pi_gt_three]








/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/






/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/













lemma LocalHypsCoreW.eight_le_L {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHypsCoreW.L_pos {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 0 < p.L := by
  linarith [hF.eight_le_L]








end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas




variable {cϱ : ℝ} {p : Setting} {F : LocalFun}




end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


















/-- The grid: `τ_k ∈ [T, 2T]` for `0 ≤ k < d` (§2.2 "τ_0,…,τ_{d−1} ∈ [T,2T)"), and `d ≤ LT/2π`. -/
lemma Setting.d_le (p : Setting) (h : 0 ≤ p.L * p.T) : (p.d : ℝ) ≤ p.L * p.T / (2 * π) :=
  Nat.floor_le (by positivity)




end TraceAnalytic

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.EndsCore
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (§5, §5.3 of the paper), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

TARGET (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X)))

PAPER (§5.3, verbatim): "For T ≥ T₀,  tr G̃² = 𝓜 + O(L l log l (l² + X)),
  𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'."

ROUTE (paper's, §5.3, with two simplifications that only change absolute constants):
* [eq:trG2int]  L² tr G̃² = Σ_{k,l<d} G_{kl}² = ∬_{ℝ²} K(τ,τ')² ν(τ)ν(τ') dτdτ',
  K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k)φ̂(τ'−τ_k) [eq:Kdef]  — here a product of two integrals and a
  FINITE sum, so no Fubini beyond ∫(f)·∫(g) = ∬ f⊗g.
* K_∞ := Σ_{k∈ℤ} φ̂(τ−τ_k)φ̂(τ'−τ_k) = L Φ(τ−τ') by [lem:poisson] (LocalHyps.poisson), so
  ∬_{I×I} K_∞² νν' = L² 𝓜, and  L²(tr G̃² − 𝓜)·L² … precisely:
  Σ G² − L²𝓜·… = 𝓔₁ + 𝓔₂,  𝓔₁ := ∬_{I×I}(K² − K_∞²)νν',  𝓔₂ := ∬_{ℝ²∖I×I} K²νν'.
* [eq:Kbounds]  |K|, |K_∞| ≤ L² (paper: aL²; a ≤ 1);  |K_out| = |K_∞ − K| handled by the
  weighted AM–GM  |Σ_{k∉[0,d)} a_k b_k| ≤ ½(s ρ(τ) + ρ(τ')/s), ρ(τ) := Σ_{k∉[0,d)} φ̂(τ−τ_k)²
  = aL² − Σ_{k<d} φ̂(τ−τ_k)² (Poisson diagonal — a FINITE expression), with s := g(τ')/g(τ),
  g := (1 + dist(·,∂I))⁻².  This replaces the paper's (∫_I ψ_k)²-sum (§5.3) and gives
  |𝓔₁| ≤ 2L²B²(∫_I ρ/g)(∫_I g) ≪ L²B²·L·l ≤ L³B² l log l  — within the lemma's error (the paper
  gets L³B² log L here; the slack l is free since 𝓔₂ is the dominant term anyway).
* 𝓔₂ exactly as the paper (§5.3): |𝓔₂| ≤ 2L² Σ_{k<d}(∫_{I^c}ψ_k|ν|)(∫_ℝ ψ_k|ν|),
  second factor ≤ 3Ψ₀B, Σ_k first factor = ∫_{I^c}|ν|σ ≪ BLl via the grid bound
  σ(τ) ≤ ψ(Δ) + h⁻¹∫_Δ^∞ψ, σ ≤ d ψ(Δ); for the far range we use log⁺x ≤ 2√x instead of
  integrating logarithms (constants only).
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X: Zeta23/PiFacts.lean
  (from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

FILE LAYOUT:
  EndsCore.lean (this file) — defs, continuity/integrability, [eq:trG2int],
     decomposition, ψ toolkit, [eq:Kbounds] pointwise;
  EndsE1.lean — calE1_bound;   EndsE2.lean (1-D estimates N1/N2 in EndsNu.lean,
     weights in EndsWeighted.lean) — calE2_bound;
  Ends.lean — assembly lem_ends' / lem_ends (proved from the two bounds).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

/-! The ψ majorant `psiA cϱ p r = min(L, 2/|r|, c_ϱ/(w r²))` [eq:psidef] and the [eq:psiints]
facts (psi_integrable, psi_sq_integrable, integral_psi_Ioi_le, integral_psi_sq_le, phiHat_le_psi,
Phi_le_psi) are in Zeta23/PrimeSideA (`LocalHyps`). -/



variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)

/-! ν-GENERIC LAYER (for Theorem E): every object below that involves the density is
stated for an ABSTRACT `ν : ℝ → ℝ` (hypotheses: `Continuous ν` and `NuBound p B ν` for a free
`B ≥ 0`); ζ is the instantiation `ν := Zeta23.nuX p.X`, `B := Bconst p` (bridges by `rfl`). -/





/-! ## [eq:Kdef] -/




/-! All double integrals below are integrals over `ℝ × ℝ` w.r.t. `volume` (= `volume.prod
volume`), restricted to `I ×ˢ I` or its complement where indicated — the same spelling as
`Mform` in Zeta23/PrimeSideA/Defs.lean. -/






variable {p F ν}

section Structure
variable {B : ℝ}
/-! ## [eq:trG2int] and the decomposition -/







/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/


















end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem psiA_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    psiA cϱ p r = min p.L (min (2 / |r|) (cϱ / (p.w * r ^ 2))) := by
  simp [psiA, hr]






theorem psiA_nonneg (hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w) (r : ℝ) : 0 ≤ psiA cϱ p r := by
  by_cases hr : r = 0
  · simp [psiA, hr, hL]
  · rw [psiA_of_ne_zero hr]
    refine le_min hL (le_min (by positivity) (by positivity))





theorem psiA_nonneg_of (hF : LocalHypsCoreW cϱ p F) (r : ℝ) : 0 ≤ psiA cϱ p r :=
  psiA_nonneg hF.L_pos.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w]) r











end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}









/-! ### K_out pointwise (weighted AM–GM), for 𝓔₁ -/





end Kbounds


end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.EndsNu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], the two one-dimensional ν-weighted ψ estimates feeding the 𝓔₂ bound
(§5.3 of the paper).  Consumed by Zeta23/PrimeSideA/EndsE2.lean.

* N1 `nu_weight_bound` (§5.3: "In the second factor, the range |τ'−τ_k| ≤ 2T has |τ'| ≤ 4T and
  contributes at most 2Ψ₀B; on |τ'−τ_k| =: r > 2T we have |τ'| ≤ 2r, |ν_X(τ')| ≤ B + log(r/T) and
  ψ(r) ≤ c_ϱ r⁻², contributing ≪ B/T. So the second factor is ≤ 3Ψ₀B uniformly in k."):
      ∫_ℝ ψ(τ−a) |ν_X(τ)| dτ ≤ (2Ψ + 5c_ϱ)·B   for a ∈ I = [T,2T],  Ψ := 4 + 2 log(c_ϱL/4w) ≥ Ψ₀.
  Route (constants only differ): |ν_X(τ)| ≤ B + log⁺(|τ|/4T) ≤ B + 2√(|τ|/4T) ≤ B + 2 + 2√(|τ−a|/4T)
  for |a| ≤ 2T, so the integral is ≤ (B+2)∫ψ + T^{-1/2}∫ψ(r)√|r| dr ≤ (B+2)·2Ψ + 2L + 4c_ϱ/w.
* N2 `nu_grid_bound` (§5.3: "The sum over k of the first factor equals ∫_{τ∉I}|ν_X(τ)|σ(τ)dτ with
  σ(τ) := Σ_{k<d} ψ(τ−τ_k) … Hence ∫_{τ∉I}|ν_X|σ ≪ BLl"):
      ∫_{ℝ∖I} |ν_X(τ)| σ(τ) dτ ≤ CN2(c_ϱ)·B·L·l.
Here ψ = `psiA cϱ p` [eq:psidef], B = `B` = l + 4√X and `NuBound p` = [eq:Bdef]
(discharged by nuX_abs_le), all from Zeta23/PrimeSideA/EndsCore.lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}









/-! ### N2: reduction to the half-line and the majorant -/





















/-! ### N2: integrating the majorant -/


/-- rpow form of the far majorant on Δ > 0. -/
lemma Mfar_eq_rpow (hT : 0 < p.T) {Δ : ℝ} (hΔ : 0 < Δ) :
    Mfar cϱ p B Δ = p.d * (cϱ / p.w) *
      (B * Δ ^ (-2:ℝ) + (2 / Real.sqrt p.T) * Δ ^ (-(3/2):ℝ)) := by
  unfold Mfar
  have hw : Δ ^ (-2:ℝ) = (Δ ^ 2)⁻¹ := by rw [Real.rpow_neg hΔ.le, Real.rpow_two]
  have h32 : Δ ^ (-(3/2):ℝ) = Δ ^ (1/2:ℝ) / Δ ^ 2 := by
    rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hΔ, Real.rpow_two]
  rw [hw, h32, Real.sqrt_div hΔ.le, Real.sqrt_eq_rpow]
  have : Δ ^ 2 ≠ 0 := by positivity
  have : Real.sqrt p.T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  field_simp

lemma Mfar_integrableOn (_hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) :
    IntegrableOn (Mfar cϱ p B) (Ioi (2 * p.T)) := by
  have h2T : 0 < 2 * p.T := by linarith
  have hg : IntegrableOn (fun Δ : ℝ => p.d * (cϱ / p.w) *
      (B * Δ ^ (-2:ℝ) + (2 / Real.sqrt p.T) * Δ ^ (-(3/2):ℝ))) (Ioi (2 * p.T)) :=
    ((((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) h2T).const_mul _).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2):ℝ) < -1) h2T).const_mul _)).const_mul _)
  refine hg.congr_fun (fun Δ hΔ => ?_) measurableSet_Ioi
  exact (Mfar_eq_rpow hT (lt_trans h2T hΔ)).symm

lemma Mtot_integrable (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) : Integrable (Mtot cϱ p B) := by
  unfold Mtot
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr (Mnear_integrableOn hF hT)).add
    ((integrable_indicator_iff measurableSet_Ioi).mpr (Mfar_integrableOn hF hT))

lemma integral_Mtot_eq (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) :
    ∫ Δ in Ioi 0, Mtot cϱ p B Δ
      = (∫ Δ in Ioc 0 (2 * p.T), Mnear cϱ p B Δ) + ∫ Δ in Ioi (2 * p.T), Mfar cϱ p B Δ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun Δ hΔ => ?_)]
  · unfold Mtot
    rw [integral_add ((integrable_indicator_iff measurableSet_Ioc).mpr (Mnear_integrableOn hF hT))
      ((integrable_indicator_iff measurableSet_Ioi).mpr (Mfar_integrableOn hF hT)),
      integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi]
  · unfold Mtot
    have hΔ' : Δ ≤ 0 := not_lt.mp hΔ
    rw [indicator_of_notMem (fun h : Δ ∈ Ioc 0 (2 * p.T) => not_lt.mpr hΔ' h.1),
      indicator_of_notMem (fun h : Δ ∈ Ioi (2 * p.T) => not_lt.mpr hΔ' (lt_trans (by linarith) h)),
      add_zero]




/-- log(2T) = log(4π) + l ≤ l + 12. -/
lemma log_two_mul_T_le (hT : 0 < p.T) : Real.log (2 * p.T) ≤ p.l + 12 := by
  have h1 : 2 * p.T = (4 * π) * (p.T / (2 * π)) := by field_simp; ring
  have h4π : 0 < 4 * π := by positivity
  have h2 : Real.log (2 * p.T) = Real.log (4 * π) + p.l := by
    rw [h1, Real.log_mul h4π.ne' (by positivity)]
    rfl
  have h3 : Real.log (4 * π) ≤ 4 * π - 1 := Real.log_le_sub_one_of_pos h4π
  have h4 : π < 3.15 := Real.pi_lt_d2
  rw [h2]
  linarith




end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem solution (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB8 : 8 ≤ B) (hT : 2 * π * Real.exp 8 ≤ p.T) :
    ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + p.L * cϱ * B) := by
  have hl8 : 8 ≤ p.l := Setting.le_l_of_T hT
  have hT1 : 1 ≤ p.T := Setting.one_le_T (by norm_num) hT
  have hT0 : 0 < p.T := by linarith
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hc : (0:ℝ) ≤ cϱ := by linarith
  have hw1 := hF.one_le_w
  have hw : 0 < p.w := by linarith
  have hB : 0 ≤ B := by linarith
  -- the set-up
  have hint := integrableOn_sigma_mul_abs_nuX hνc hF hν hT1
  have hcompl : (p.I)ᶜ = Iio p.T ∪ Ioi (2 * p.T) := by
    ext x
    simp only [Setting.I, Zeta23.Iwin, Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi, not_and_or, not_le]
  rw [hcompl] at hint ⊢
  have hintL := hint.mono_set Set.subset_union_left
  have hintR := hint.mono_set Set.subset_union_right
  have hdisj : Disjoint (Iio p.T) (Ioi (2 * p.T)) :=
    Set.disjoint_left.mpr fun x hx hx' => by
      simp only [Set.mem_Iio, Set.mem_Ioi] at hx hx'; linarith
  rw [setIntegral_union hdisj measurableSet_Ioi hintL hintR]
  -- each side ≤ ∫_0^∞ Mtot
  have hleft : ∫ τ in Iio p.T, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ ∫ Δ in Ioi 0, Mtot cϱ p B Δ := by
    calc ∫ τ in Iio p.T, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
        ≤ ∫ τ in Iio p.T, Mtot cϱ p B (p.T - τ) :=
          setIntegral_mono_on hintL ((Mtot_integrable (B := B) hF hT0).comp_sub_left p.T).integrableOn
            measurableSet_Iio (fun τ hτ => dom_left hF hν hT0 hτ)
      _ = ∫ Δ in Ioi 0, Mtot cϱ p B Δ := setIntegral_Iio_comp_sub_left _ _
  have hright : ∫ τ in Ioi (2 * p.T), (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ ∫ Δ in Ioi 0, Mtot cϱ p B Δ := by
    calc ∫ τ in Ioi (2 * p.T), (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
        ≤ ∫ τ in Ioi (2 * p.T), Mtot cϱ p B (τ - 2 * p.T) :=
          setIntegral_mono_on hintR ((Mtot_integrable (B := B) hF hT0).comp_sub_right (2 * p.T)).integrableOn
            measurableSet_Ioi (fun τ hτ => dom_right hF hν hT0 hτ)
      _ = ∫ Δ in Ioi 0, Mtot cϱ p B Δ := setIntegral_Ioi_comp_sub_right _ _
  -- the majorant's integral
  set Ψ' := ∫ r in Ioi 0, psiA cϱ p r with hΨ'
  have hΨ0 : 0 ≤ Ψ' := setIntegral_nonneg measurableSet_Ioi fun r _ => psiA_nonneg_of hF r
  have hM : ∫ Δ in Ioi 0, Mtot cϱ p B Δ
      ≤ B * (Ψ' + p.L / (2 * π) * (Ψ' + cϱ / p.w * Real.log (2 * p.T)))
        + p.d / p.T * (cϱ / p.w) * (B / 2 + 4) := by
    rw [integral_Mtot_eq hF hT0]
    exact add_le_add (integral_Mnear_le hF hB hT1) (integral_Mfar_le hF hB hT1)
  -- elementary bounds on the ingredients
  have hΨ1 : Ψ' ≤ 2 + cϱ * p.L / 2 := by
    have h1 : Ψ' ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w)) := hF.integral_psi_Ioi_le
    have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
    have h2 := Real.log_le_sub_one_of_pos harg
    have h3 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    linarith
  have hlog := log_two_mul_T_le (p := p) hT0
  have hcw : cϱ / p.w ≤ cϱ := div_le_self hc hw1
  have hdT : p.d / p.T ≤ p.L := by
    rw [div_le_iff₀ hT0]
    have := p.d_le (by positivity : 0 ≤ p.L * p.T)
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, mul_pos hL hT0]
  have h2π : p.L / (2 * π) ≤ p.L := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  have hB2 : B / 2 + 4 ≤ B := by linarith
  -- near ≤ B (Ψ₁ + L (Ψ₁ + c (l + 12))),  Ψ₁ = 2 + cL/2
  have hinner : Ψ' + cϱ / p.w * Real.log (2 * p.T) ≤ (2 + cϱ * p.L / 2) + cϱ * (p.l + 12) := by
    have hlog0 : 0 ≤ Real.log (2 * p.T) := Real.log_nonneg (by linarith)
    have : cϱ / p.w * Real.log (2 * p.T) ≤ cϱ * (p.l + 12) :=
      mul_le_mul hcw hlog hlog0 hc
    linarith
  have hinner0 : 0 ≤ Ψ' + cϱ / p.w * Real.log (2 * p.T) := by
    have hlog0 : 0 ≤ Real.log (2 * p.T) := Real.log_nonneg (by linarith)
    positivity
  have hnear : B * (Ψ' + p.L / (2 * π) * (Ψ' + cϱ / p.w * Real.log (2 * p.T)))
      ≤ B * ((2 + cϱ * p.L / 2) + p.L * ((2 + cϱ * p.L / 2) + cϱ * (p.l + 12))) := by
    refine mul_le_mul_of_nonneg_left (add_le_add hΨ1 ?_) hB
    exact mul_le_mul h2π hinner hinner0 hL.le
  have hfar : p.d / p.T * (cϱ / p.w) * (B / 2 + 4) ≤ p.L * cϱ * B := by
    apply mul_le_mul (mul_le_mul hdT hcw (by positivity) hL.le) hB2 (by positivity) (by positivity)
  -- polynomial endgame
  have hside : ∫ Δ in Ioi 0, Mtot cϱ p B Δ
      ≤ B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B := by
    refine hM.trans (add_le_add (hnear.trans (le_of_eq ?_)) hfar)
    ring
  linarith [hleft, hright, hside]
