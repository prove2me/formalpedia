-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_calE1_le_maj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:30:45.553371+00:00
-- url     : https://prove2.me/submissions/edca26f8-6809-4948-9fe4-e52f7ad38e09

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
import Theorems.Thm_Zeta23_PrimeSide_abs_E1integrand_le_majK1

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


theorem Kfun_continuous (hF : LocalHypsCoreW cϱ p F) :
    Continuous (fun q : ℝ × ℝ => Kfun p F q.1 q.2) := by
  have := hF.phiHat_cont
  unfold Kfun
  fun_prop

theorem trG2integrand_continuous (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) :
    Continuous (trG2integrand p F ν) := by
  have h1 := hνc
  have h2 := Kfun_continuous hF
  unfold trG2integrand
  fun_prop

theorem KinfIntegrand_continuous (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) :
    Continuous (KinfIntegrand p F ν) := by
  have h1 := hνc
  have h2 : Continuous F.Phi := hF.Phi_contDiff.continuous
  unfold KinfIntegrand Kinf
  fun_prop

theorem isCompact_sqI : IsCompact (sqI p) := isCompact_Icc.prod isCompact_Icc

theorem measurableSet_sqI : MeasurableSet (sqI p) := measurableSet_Icc.prod measurableSet_Icc

/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/


















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

theorem distB_nonneg {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 ≤ distB p τ := by
  unfold distB; rcases hτ with ⟨h1, h2⟩; exact le_min (by linarith) (by linarith)

theorem gwt_pos {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 < gwt p τ := by
  unfold gwt; have := distB_nonneg hτ; positivity






/-! ### The majorant for ρ on I -/






/-! ### The weight integrals -/



/-! ### Assembly -/

section Bounds
variable (cϱ lam : ℝ)




end Bounds

section BoundsCor
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}


variable (cϱ lam : ℝ)


end BoundsCor

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem solution (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (_hT : 0 < p.T) :
    |calE1 p F ν| ≤ ∫ q in sqI p, majK1 p F ν q := by
  have hcpt : IsCompact (sqI p) := isCompact_sqI
  have hfi : IntegrableOn (fun q => trG2integrand p F ν q - KinfIntegrand p F ν q) (sqI p) :=
    ((trG2integrand_continuous hνc hF).sub (KinfIntegrand_continuous hνc hF)).continuousOn
      |>.integrableOn_compact hcpt
  -- integrability of majK1 on the compact square
  have hρc : Continuous (rho p F) := by
    have := hF.phiHat_cont; unfold rho; fun_prop
  have hdistc : Continuous (distB p) := by unfold distB; fun_prop
  have hgc : ContinuousOn (gwt p) (Icc p.T (2 * p.T)) := by
    unfold gwt
    refine ContinuousOn.inv₀ (by fun_prop) fun τ hτ => ?_
    have := distB_nonneg (p := p) hτ; positivity
  have hρg : ContinuousOn (fun τ => rho p F τ / gwt p τ) (Icc p.T (2 * p.T)) :=
    hρc.continuousOn.div hgc fun τ hτ => (gwt_pos hτ).ne'
  have hfst : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.1) (sqI p) := fun hf =>
    hf.comp continuous_fst.continuousOn fun q hq => hq.1
  have hsnd : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.2) (sqI p) := fun hf =>
    hf.comp continuous_snd.continuousOn fun q hq => hq.2
  have hνa : ContinuousOn (fun τ => |ν τ|) (Icc p.T (2 * p.T)) := hνc.abs.continuousOn
  have hM1c : ContinuousOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    (hfst hρg).mul (hsnd hgc)
  have hM2c : ContinuousOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    (hfst hgc).mul (hsnd hρg)
  have hc : ContinuousOn (majK1 p F ν) (sqI p) := by
    have := ((hM1c.add hM2c).const_smul (p.L ^ 2)).mul ((hfst hνa).mul (hsnd hνa))
    refine this.congr fun q hq => ?_
    simp only [majK1, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  have hmi : IntegrableOn (majK1 p F ν) (sqI p) := hc.integrableOn_compact hcpt
  unfold calE1
  have step1 := norm_integral_le_integral_norm (μ := volume.restrict (sqI p))
    (fun q => trG2integrand p F ν q - KinfIntegrand p F ν q)
  rw [Real.norm_eq_abs] at step1
  refine step1.trans ?_
  refine setIntegral_mono_on hfi.norm hmi measurableSet_sqI fun q hq => ?_
  rw [Real.norm_eq_abs]
  exact abs_E1integrand_le_majK1 hF hq
