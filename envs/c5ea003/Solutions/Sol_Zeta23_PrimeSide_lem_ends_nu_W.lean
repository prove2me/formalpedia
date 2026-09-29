-- Prove2me | solution 1 for Zeta23.PrimeSide.lem_ends_nu_W
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:27:20.859778+00:00
-- url     : https://prove2.me/submissions/2db24c7d-41ec-4250-8ed5-79f89eb2fd2d

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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
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
import Definitions.Def_Zeta23_PrimeSideA_EndsE1
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Theorems.Thm_Zeta23_PrimeSide_abs_calE1_le_maj
import Theorems.Thm_Zeta23_PrimeSide_abs_gkl_le
import Theorems.Thm_Zeta23_PrimeSide_abs_trG2integrand_le
import Theorems.Thm_Zeta23_PrimeSide_calE1_maj_bound
import Theorems.Thm_Zeta23_PrimeSide_calE2_maj_bound
import Theorems.Thm_Zeta23_PrimeSide_eq_trG2int
import Theorems.Thm_Zeta23_PrimeSide_majK2_integrable

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




theorem KinfIntegrand_continuous (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) :
    Continuous (KinfIntegrand p F ν) := by
  have h1 := hνc
  have h2 : Continuous F.Phi := hF.Phi_contDiff.continuous
  unfold KinfIntegrand Kinf
  fun_prop

theorem isCompact_sqI : IsCompact (sqI p) := isCompact_Icc.prod isCompact_Icc

theorem measurableSet_sqI : MeasurableSet (sqI p) := measurableSet_Icc.prod measurableSet_Icc

/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/









theorem gkl_continuous (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (k l : ℤ) :
    Continuous (gkl p F ν k l) := by
  have h1 := hνc
  have h2 := hF.phiHat_cont
  unfold gkl
  fun_prop


theorem gkl_integrable (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hT : 1 ≤ p.T) (hB : 0 ≤ B) (k l : ℤ) : Integrable (gkl p F ν k l) := by
  set C : ℝ := 4 * (p.L + cϱ / p.w) ^ 2 * (1 + p.tau k ^ 2) * (1 + p.tau l ^ 2) * (B + 1)
  refine Integrable.mono' (g := fun τ : ℝ => C * (1 + τ ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul C)
    (gkl_continuous hνc hF k l).aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs]
  exact abs_gkl_le hF hν hT hB k l τ


/-- pointwise: `Σ_{k,l<d} g_{kl}(τ) g_{kl}(τ') = K(τ,τ')² ν(τ)ν(τ')`. -/
theorem sum_gkl_mul_gkl (q : ℝ × ℝ) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, gkl p F ν k l q.1 * gkl p F ν k l q.2 = trG2integrand p F ν q := by
  unfold trG2integrand Kfun gkl
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The heart of "the interchange being justified by absolute convergence" (§5.3):
`K(τ,τ')² ν(τ)ν(τ')` is integrable on `ℝ²`. -/
theorem trG2integrand_integrable (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    Integrable (trG2integrand p F ν) := by
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have h : Integrable (fun q : ℝ × ℝ => ∑ k : Fin p.d, ∑ l : Fin p.d,
      gkl p F ν k l q.1 * gkl p F ν k l q.2) := by
    refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
    exact (gkl_integrable hνc hF hν hT1 hB k l).mul_prod (gkl_integrable hνc hF hν hT1 hB k l)
  exact h.congr (Filter.Eventually.of_forall fun q => sum_gkl_mul_gkl q)


/-- `∬_{I×I} K_∞² νν' = L² 𝓜` (§5.3 "note …"). -/
theorem integral_Kinf_sq : ∫ q in sqI p, KinfIntegrand p F ν q = p.L ^ 2 * MtotalNu ν p F := by
  unfold MtotalNu Mform KinfIntegrand Kinf sqI
  rw [← integral_const_mul]
  congr 1 with q
  ring

/-- The decomposition  `Σ_{k,l<d} G_{kl}² − L²𝓜 = 𝓔₁ + 𝓔₂`. -/
theorem decomp (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - p.L ^ 2 * MtotalNu ν p F
      = calE1 p F ν + calE2 p F ν := by
  have hint := trG2integrand_integrable hνc hF hν hB hT
  have h1 : IntegrableOn (trG2integrand p F ν) (sqI p) := hint.integrableOn
  have h2 : IntegrableOn (KinfIntegrand p F ν) (sqI p) :=
    (KinfIntegrand_continuous hνc hF).continuousOn.integrableOn_compact (isCompact_sqI (p := p))
  rw [eq_trG2int hνc hF hν hB hT, ← integral_Kinf_sq, calE1, calE2, integral_sub h1 h2,
    ← integral_add_compl (measurableSet_sqI (p := p)) hint]
  ring

end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}























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

-- from Zeta23.PrimeSideA.EndsE1
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₁ (§5.3).  Statement `calE1_bound` consumed by
Zeta23/PrimeSideA/Ends.lean.

ROUTE.  On I×I: |ν|,|ν'| ≤ B;  |K + K_∞| ≤ 2L² (abs_Kfun_le, abs_Kinf_le);
|K_∞ − K| ≤ (s ρ(τ) + ρ(τ')/s)/2 for every s > 0 (abs_Kinf_sub_Kfun_le), with the choice
s := g(τ')/g(τ), g(τ) := (1 + min(τ−T, 2T−τ))⁻² > 0.  Hence pointwise
  |K²−K_∞²||ν||ν'| ≤ L²B² ( ρ(τ)/g(τ)·g(τ') + g(τ)·ρ(τ')/g(τ') )
and integrating over I×I (product structure):  |𝓔₁| ≤ 2L²B² (∫_I ρ/g)(∫_I g),  ∫_I g ≤ 2.
Pointwise majorant (finite partial sums of the HasSum for ρ, ψ antitone, grid lemma):
  ρ(τ) ≤ W(τ−T) + W(2T−τ) + ψ(τ_d − τ)²,   W(Δ) := ψ(Δ)² + h⁻¹∫_{(Δ,∞)}ψ²,
and 1/g = (1+min(τ−T,2T−τ))² ≤ (1+(τ−T))², (1+(2T−τ))², (1+h+|τ_d−τ|)² respectively, so
  ∫_I ρ/g ≤ 2∫_0^T W(u)(1+u)² du + ∫_ℝ ψ(r)²(2+|r|)² dr ≪ L² + L·l   (split at 1; ψ ≤ L,
  ψ(r) ≤ (c/w)/r², ∫_{(Δ,∞)}ψ² ≤ min(8L, (c/w)²/(3Δ³)), log T ≤ 2l).
Budget: |𝓔₁| ≤ C(c_ϱ)·L²B²(L² + L l) ≤ C·L³B² l (L = λl ≤ l).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-! ### Definitions -/




/-! ### Leaf integrals -/










/-! ### Pointwise facts on I -/








/-! ### The majorant for ρ on I -/






/-! ### The weight integrals -/



/-! ### Assembly -/

section Bounds
variable (cϱ lam : ℝ)




end Bounds

section BoundsCor
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}


variable (cϱ lam : ℝ)

/-- **Bound for 𝓔₁** (cf. §5.3): `|𝓔₁| ≤ C · L³ B² l` for `T ≥ T₀` (corollary). -/
theorem calE1_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν →
      |calE1 p F ν| ≤ C * (p.L ^ 3 * B ^ 2 * p.l) := by
  obtain ⟨C, T₀, h⟩ := calE1_maj_bound cϱ lam
  refine ⟨C, max T₀ 1, fun p F B ν hplam hT hF hL2l hνc hν => ?_⟩
  have hT0 : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hTpos : 0 < p.T := by linarith [(le_max_right T₀ 1).trans hT]
  exact (abs_calE1_le_maj hνc hF hTpos).trans (h p F B ν hplam hT0 hF hL2l hνc hν)

end BoundsCor

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.EndsE2
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₂ (§5.3).  Statement consumed by
Zeta23/PrimeSideA/Ends.lean.
Substrate: Zeta23/PrimeSideA/EndsWeighted.lean; 1-D estimates N1/N2 from
Zeta23/PrimeSideA/EndsNu.lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

section Assembly

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}



theorem abs_trG2integrand_le_majK2 (hF : LocalHypsCoreW cϱ p F) (q : ℝ × ℝ) :
    |trG2integrand p F ν q| ≤ majK2 cϱ p ν q := abs_trG2integrand_le hF q


/-- `|𝓔₂(ν)| ≤ ∬_{(I×I)ᶜ} majK2(ν)`. -/
theorem abs_calE2_le_maj (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB0 : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    |calE2 p F ν| ≤ ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q := by
  have hfi : Integrable (trG2integrand p F ν) := trG2integrand_integrable hνc hF hν hB0 hT
  unfold calE2
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
    (majK2_integrable hνc hF hν hB0 hT).integrableOn
    (Filter.Eventually.of_forall fun q => ?_)
  show ‖trG2integrand p F ν q‖ ≤ _
  rw [Real.norm_eq_abs]
  exact abs_trG2integrand_le_majK2 hF q


end Assembly

section Bounds
variable (cϱ lam : ℝ)





/-- **Bound for E2** (§5.3): |𝓔₂| ≤ C·L³B²·l·log l for T ≥ T₀ (corollary of the
majorant bound via |K²νν'| ≤ majK2). -/
theorem calE2_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      |calE2 p F ν| ≤ C * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
  obtain ⟨C, T₀, h⟩ := calE2_maj_bound cϱ lam
  refine ⟨C, max T₀ (2 * π), fun p F B ν hplam hT hF hL2l hνc hν hBl => ?_⟩
  have hT0 : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hT2π : 2 * π ≤ p.T := (le_max_right _ _).trans hT
  have hB0 : 0 ≤ B := le_trans (by linarith [hF.one_le_l]) hBl
  refine le_trans ?_ (h p F B ν hplam hT0 hF hL2l hνc hν hBl)
  exact abs_calE2_le_maj hνc hF hν hB0 hT2π

end Bounds

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.Ends
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (the paper, §5, §5.3), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

MAIN RESULT (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
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
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X (Zeta23/PiFacts.lean,
  from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

The proof is assembled from the 𝓔₁ and 𝓔₂ bounds (Zeta23.PrimeSideA.EndsE1/EndsE2) in the
theorems below.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide


section Main
variable (cϱ lam : ℝ)





end Main

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem solution :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      |(p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F|
        ≤ C * (p.L * p.l * Real.log p.l * B ^ 2) := by
  obtain ⟨C₁, T₁, h1⟩ := calE1_bound cϱ lam
  obtain ⟨C₂, T₂, h2⟩ := calE2_bound cϱ lam
  -- T ≥ 2π e^e gives l ≥ e ≥ 1 hence log l ≥ 1
  refine ⟨(|C₁| + |C₂|), max (max T₁ T₂) (2 * π * Real.exp (Real.exp 1)),
    fun p F B ν hplam hT hF hL2l hνc hν hBl => ?_⟩
  have hT1 : T₁ ≤ p.T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ p.T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTe : 2 * π * Real.exp (Real.exp 1) ≤ p.T := le_trans (le_max_right _ _) hT
  have hl : Real.exp 1 ≤ p.l := Setting.le_l_of_T hTe
  have hl1 : 1 ≤ p.l := le_trans (by linarith [Real.add_one_le_exp (1:ℝ)]) hl
  have hlog : 1 ≤ Real.log p.l := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hl
  have hT' : 2 * π ≤ p.T := Setting.twopi_le_T (Real.exp_pos 1).le hTe
  have hL := hF.L_pos
  have hB0 : 0 ≤ B := le_trans (by linarith) hBl
  have e1 := h1 p F B ν hplam hT1 hF hL2l hνc hν
  have e2 := h2 p F B ν hplam hT2 hF hL2l hνc hν hBl
  have hdec := decomp hνc hF hν hB0 hT'
  have hkey : (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F
      = (p.L)⁻¹ ^ 2 * (calE1 p F ν + calE2 p F ν) := by
    rw [← hdec]
    field_simp
  rw [hkey, abs_mul, abs_of_pos (by positivity)]
  have hsum : |calE1 p F ν + calE2 p F ν|
      ≤ (|C₁| + |C₂|) * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
    calc |calE1 p F ν + calE2 p F ν| ≤ |calE1 p F ν| + |calE2 p F ν| := abs_add_le _ _
      _ ≤ C₁ * (p.L ^ 3 * B ^ 2 * p.l) + C₂ * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) :=
          add_le_add e1 e2
      _ ≤ |C₁| * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l)
          + |C₂| * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
          gcongr ?_ + ?_
          · calc C₁ * (p.L ^ 3 * B ^ 2 * p.l) ≤ |C₁| * (p.L ^ 3 * B ^ 2 * p.l) := by
                  gcongr; exact le_abs_self _
              _ = |C₁| * (p.L ^ 3 * B ^ 2 * p.l) * 1 := (mul_one _).symm
              _ ≤ |C₁| * (p.L ^ 3 * B ^ 2 * p.l) * Real.log p.l := by gcongr
              _ = _ := by ring
          · exact mul_le_mul_of_nonneg_right (le_abs_self C₂) (by positivity)
      _ = _ := by ring
  calc (p.L)⁻¹ ^ 2 * |calE1 p F ν + calE2 p F ν|
      ≤ (p.L)⁻¹ ^ 2 * ((|C₁| + |C₂|) * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l)) := by gcongr
    _ = (|C₁| + |C₂|) * (p.L * p.l * Real.log p.l * B ^ 2) := by field_simp
