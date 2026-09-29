-- Prove2me | solution 1 for Zeta23.PrimeSide.rho_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:19:58.221026+00:00
-- url     : https://prove2.me/submissions/a3a2cd58-2dfe-492e-8905-697b6d672adf

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
import Theorems.Thm_Zeta23_PrimeSide_sum_grid_le_of_antitoneOn

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



















lemma Setting.d_eq_floor (p : Setting) (hL : 0 < p.L) : p.d = ⌊p.T / p.h⌋₊ := by
  simp only [Setting.d, Setting.h]
  congr 1
  field_simp



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

theorem psiA_zero : psiA cϱ p 0 = p.L := by simp [psiA]

theorem psiA_le_L (r : ℝ) : psiA cϱ p r ≤ p.L := by
  by_cases hr : r = 0
  · simp [psiA, hr]
  · rw [psiA_of_ne_zero hr]; exact min_le_left _ _



theorem psiA_even (r : ℝ) : psiA cϱ p (-r) = psiA cϱ p r := by
  simp [psiA]

theorem psiA_nonneg (hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w) (r : ℝ) : 0 ≤ psiA cϱ p r := by
  by_cases hr : r = 0
  · simp [psiA, hr, hL]
  · rw [psiA_of_ne_zero hr]
    refine le_min hL (le_min (by positivity) (by positivity))


theorem psiA_abs (r : ℝ) : psiA cϱ p |r| = psiA cϱ p r := by
  rcases le_or_gt 0 r with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, psiA_even]

/-- ψ is antitone on [0, ∞). -/
theorem psiA_antitoneOn (_hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w) :
    AntitoneOn (psiA cϱ p) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  rcases eq_or_lt_of_le ha with rfl | ha'
  · rw [psiA_zero]; exact psiA_le_L b
  · have hb' : 0 < b := lt_of_lt_of_le ha' hab
    rw [psiA_of_ne_zero ha'.ne', psiA_of_ne_zero hb'.ne', abs_of_pos ha', abs_of_pos hb']
    refine min_le_min le_rfl (min_le_min ?_ ?_)
    · exact div_le_div_of_nonneg_left (by norm_num) ha' hab
    · exact div_le_div_of_nonneg_left hc (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) hw.le)


theorem psiA_nonneg_of (hF : LocalHypsCoreW cϱ p F) (r : ℝ) : 0 ≤ psiA cϱ p r :=
  psiA_nonneg hF.L_pos.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w]) r





/-- ψ² is antitone on [0,∞) (ψ ≥ 0 antitone). -/
theorem psiA_sq_antitoneOn (hF : LocalHypsCoreW cϱ p F) :
    AntitoneOn (fun r => psiA cϱ p r ^ 2) (Set.Ici 0) := by
  have hc : 0 ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  intro a ha b hb hab
  have h := psiA_antitoneOn hF.L_pos.le hc hw ha hb hab
  show psiA cϱ p b ^ 2 ≤ psiA cϱ p a ^ 2
  exact pow_le_pow_left₀ (psiA_nonneg_of hF b) h 2

/-- same for ψ²: Σ_{j<n} ψ(Δ + j h)² ≤ ψ(Δ)² + h⁻¹ ∫_{(Δ,∞)} ψ². -/
theorem sum_psiA_sq_grid_le (hF : LocalHypsCoreW cϱ p F) {Δ h : ℝ} (hΔ : 0 ≤ Δ) (hh : 0 < h) (n : ℕ) :
    ∑ j ∈ Finset.range n, psiA cϱ p (Δ + j * h) ^ 2
      ≤ psiA cϱ p Δ ^ 2 + h⁻¹ * ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2 :=
  sum_grid_le_of_antitoneOn (f := fun r => psiA cϱ p r ^ 2) (psiA_sq_antitoneOn hF)
    (fun _ _ => sq_nonneg _) hΔ hh hF.psi_sq_integrable.integrableOn n





end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


lemma sum_Ico_int_eq (p : Setting) (F : LocalFun) (τ : ℝ) :
    ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2
      = ∑ k : Fin p.d, F.phiHat (τ - p.tau (k : ℕ)) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => F.phiHat (τ - p.tau (n : ℕ)) ^ 2) p.d]
  rw [show Finset.Ico (0:ℤ) (p.d : ℤ) = (Finset.range p.d).image (fun n : ℕ => (n : ℤ)) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hd⟩
      exact ⟨k.toNat, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega]
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]

lemma hasSum_total (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (F.a * p.L ^ 2) := by
  have h := hF.poisson τ τ
  rw [sub_self, hF.Phi_zero] at h
  have h2 : HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (p.L * (F.a * p.L)) := by
    refine HasSum.congr_fun h fun k => ?_
    rw [sq]
  rwa [show p.L * (F.a * p.L) = F.a * p.L ^ 2 by ring] at h2


/-- `ρ(τ) = Σ_{k∉[0,d)} φ̂(τ−τ_k)²` as a `HasSum` over the complement of `range d` in ℤ
(from LocalHyps.poisson τ τ and Phi_zero). -/
theorem hasSum_rho (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    HasSum (fun k : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} => F.phiHat (τ - p.tau k) ^ 2)
      (rho p F τ) := by
  have htot := hasSum_total hF τ
  refine (Finset.hasSum_compl_iff (f := fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2)
    (Finset.Ico (0:ℤ) (p.d : ℤ))).2 ?_
  have he : rho p F τ + ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2
      = F.a * p.L ^ 2 := by
    unfold rho
    rw [sum_Ico_int_eq]
    ring
  rw [he]
  exact htot




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








/-! ### The majorant for ρ on I -/

/-- `τ_d = T + d h > 2T − h` (since `d = ⌊T/h⌋`). -/
theorem tau_d_gt (hL : 0 < p.L) (_hT : 0 < p.T) : 2 * p.T - p.h < p.tau p.d := by
  have hh : 0 < p.h := by unfold Setting.h; positivity
  have hd : p.d = ⌊p.T / p.h⌋₊ := Setting.d_eq_floor p hL
  have hlt : p.T / p.h < (p.d : ℝ) + 1 := by rw [hd]; exact Nat.lt_floor_add_one _
  have : p.T < ((p.d : ℝ) + 1) * p.h := by rwa [div_lt_iff₀ hh] at hlt
  rw [Setting.tau]
  push_cast
  nlinarith

/-- generic: a finite sum dominated termwise by a grid function is ≤ the grid sum over a range. -/
theorem sum_le_sum_range_of_injOn {α : Type*} (S : Finset α) (ι : α → ℕ) (hι : Set.InjOn ι S)
    (G : ℕ → ℝ) (hG : ∀ m, 0 ≤ G m) (f : α → ℝ) (hf : ∀ k ∈ S, f k ≤ G (ι k)) :
    ∑ k ∈ S, f k ≤ ∑ m ∈ Finset.range (S.sup ι + 1), G m := by
  calc ∑ k ∈ S, f k ≤ ∑ k ∈ S, G (ι k) := Finset.sum_le_sum hf
    _ = ∑ m ∈ S.image ι, G m := (Finset.sum_image hι).symm
    _ ≤ ∑ m ∈ Finset.range (S.sup ι + 1), G m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => hG m)
        intro m hm
        rw [Finset.mem_image] at hm
        obtain ⟨k, hk, rfl⟩ := hm
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.le_sup hk)


theorem h_pos (hF : LocalHypsCoreW cϱ p F) : 0 < p.h := by
  unfold Setting.h; have := hF.L_pos; positivity


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

theorem solution (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) {τ : ℝ}
    (hτ : τ ∈ Icc p.T (2 * p.T)) :
    rho p F τ ≤ Wfun cϱ p (τ - p.T) + Wfun cϱ p (2 * p.T - τ) + psiA cϱ p (p.tau p.d - τ) ^ 2 := by
  have hL := hF.L_pos
  have hh := h_pos hF
  have hΔL : 0 ≤ τ - p.T := by linarith [hτ.1]
  have hΔR : 0 ≤ 2 * p.T - τ := by linarith [hτ.2]
  have htd := tau_d_gt hL hT
  have hψ0 := psiA_nonneg_of hF
  have hanti' : AntitoneOn (psiA cϱ p) (Set.Ici 0) :=
    psiA_antitoneOn hL.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w])
  refine hasSum_le_of_sum_le (hasSum_rho hF τ) (fun S => ?_)
  -- termwise φ̂² ≤ ψ²
  have hterm : ∀ k : {k : ℤ // k ∉ Finset.Ico (0:ℤ) p.d},
      F.phiHat (τ - p.tau k) ^ 2 ≤ psiA cϱ p (τ - p.tau k) ^ 2 := by
    intro k
    have h := hF.phiHat_le_psi (τ - p.tau k)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- split S into k < 0 and k ≥ d
  set Sm := S.filter (fun k => k.1 < 0) with hSm
  set Sp := S.filter (fun k => ¬ k.1 < 0) with hSp
  -- LEFT: k < 0, τ − τ_k = (τ−T) + (−k)h
  have hleft : ∑ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2 ≤ Wfun cϱ p (τ - p.T) := by
    set ι : {k : ℤ // k ∉ Finset.Ico (0:ℤ) p.d} → ℕ := fun k => (-k.1).toNat with hι
    set G : ℕ → ℝ := fun m => psiA cϱ p ((τ - p.T) + m * p.h) ^ 2 with hG
    have hinj : Set.InjOn ι Sm := by
      intro a ha b hb hab
      simp only [hSm, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only [hι] at hab
      apply Subtype.ext
      have := congrArg (fun n : ℕ => (n : ℤ)) hab
      beta_reduce at this
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at this
      omega
    have hf : ∀ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2 ≤ G (ι k) := by
      intro k hk
      simp only [hSm, Finset.mem_filter] at hk
      have hk0 : k.1 < 0 := hk.2
      have hcast : ((ι k : ℕ) : ℝ) = -(k.1 : ℝ) := by
        simp only [hι]
        have : ((-k.1).toNat : ℤ) = -k.1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      have : τ - p.tau k = (τ - p.T) + (ι k) * p.h := by
        rw [hcast, Setting.tau]; ring
      simp only [hG]
      rw [← this]
    calc ∑ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2
        ≤ ∑ m ∈ Finset.range (Sm.sup ι + 1), G m :=
          sum_le_sum_range_of_injOn Sm ι hinj G (fun m => sq_nonneg _) _ hf
      _ ≤ Wfun cϱ p (τ - p.T) := by
          rw [hG, Wfun]
          exact sum_psiA_sq_grid_le hF hΔL hh _
  -- RIGHT: k ≥ d.  Split k = d (the stray term) from k ≥ d+1.
  have hright : ∑ k ∈ Sp, psiA cϱ p (τ - p.tau k) ^ 2
      ≤ Wfun cϱ p (2 * p.T - τ) + psiA cϱ p (p.tau p.d - τ) ^ 2 := by
    have hSp_ge : ∀ k ∈ Sp, (p.d : ℤ) ≤ k.1 := by
      intro k hk
      simp only [hSp, Finset.mem_filter, not_lt] at hk
      have hk2 := k.2
      simp only [Finset.mem_Ico, not_and, not_lt] at hk2
      exact hk2 hk.2
    set Sd := Sp.filter (fun k => k.1 = (p.d : ℤ)) with hSd
    set Sq := Sp.filter (fun k => ¬ k.1 = (p.d : ℤ)) with hSq
    -- stray term: at most one element, value ψ(τ − τ_d)² = ψ(τ_d − τ)²
    have hstray : ∑ k ∈ Sd, psiA cϱ p (τ - p.tau k) ^ 2 ≤ psiA cϱ p (p.tau p.d - τ) ^ 2 := by
      have hval : ∀ k ∈ Sd, psiA cϱ p (τ - p.tau k) ^ 2 = psiA cϱ p (p.tau p.d - τ) ^ 2 := by
        intro k hk
        simp only [hSd, Finset.mem_filter] at hk
        have hk2 : (k : ℤ) = ((p.d : ℕ) : ℤ) := hk.2
        rw [hk2, ← psiA_even, neg_sub]
      have hcard : Sd.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [hSd, Finset.mem_filter] at ha hb
        exact Subtype.ext (ha.2.trans hb.2.symm)
      rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
      have : (Sd.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith [sq_nonneg (psiA cϱ p (p.tau p.d - τ))]
    -- k ≥ d+1: τ_k − τ = (τ_d + h − τ) + j h ≥ (2T−τ) + j h, j = k − d − 1
    have hfar : ∑ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2 ≤ Wfun cϱ p (2 * p.T - τ) := by
      set ι : {k : ℤ // k ∉ Finset.Ico (0:ℤ) p.d} → ℕ := fun k => (k.1 - p.d - 1).toNat with hι
      set G : ℕ → ℝ := fun m => psiA cϱ p ((2 * p.T - τ) + m * p.h) ^ 2 with hG
      have hSq_ge : ∀ k ∈ Sq, (p.d : ℤ) + 1 ≤ k.1 := by
        intro k hk
        simp only [hSq, Finset.mem_filter] at hk
        have := hSp_ge k hk.1
        omega
      have hinj : Set.InjOn ι Sq := by
        intro a ha b hb hab
        have ha' := hSq_ge a ha
        have hb' := hSq_ge b hb
        simp only [hι] at hab
        apply Subtype.ext
        have := congrArg (fun n : ℕ => (n : ℤ)) hab
        beta_reduce at this
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at this
        omega
      have hf : ∀ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2 ≤ G (ι k) := by
        intro k hk
        have hk' := hSq_ge k hk
        have hcast : ((ι k : ℕ) : ℝ) = (k.1 : ℝ) - p.d - 1 := by
          simp only [hι]
          have : ((k.1 - p.d - 1).toNat : ℤ) = k.1 - p.d - 1 := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        -- τ_k − τ = (τ_d + h − τ) + (ι k) h
        have hdist : p.tau k - τ = (p.tau p.d + p.h - τ) + (ι k) * p.h := by
          rw [hcast, Setting.tau, Setting.tau]; push_cast; ring
        have hge : (2 * p.T - τ) + (ι k) * p.h ≤ p.tau k - τ := by
          rw [hdist]; have : (0:ℝ) ≤ (ι k) * p.h := by positivity
          linarith
        have hnn : 0 ≤ (2 * p.T - τ) + (ι k) * p.h := by positivity
        rw [hG]
        simp only
        rw [← psiA_abs (τ - p.tau k), abs_sub_comm, abs_of_nonneg (le_trans hnn hge)]
        exact pow_le_pow_left₀ (hψ0 _) (hanti' hnn (le_trans hnn hge) hge) 2
      calc ∑ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2
          ≤ ∑ m ∈ Finset.range (Sq.sup ι + 1), G m :=
            sum_le_sum_range_of_injOn Sq ι hinj G (fun m => sq_nonneg _) _ hf
        _ ≤ Wfun cϱ p (2 * p.T - τ) := by
            rw [hG, Wfun]
            exact sum_psiA_sq_grid_le hF hΔR hh _
    calc ∑ k ∈ Sp, psiA cϱ p (τ - p.tau k) ^ 2
        = ∑ k ∈ Sd, psiA cϱ p (τ - p.tau k) ^ 2 + ∑ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2 :=
          (Finset.sum_filter_add_sum_filter_not Sp (fun k => k.1 = (p.d : ℤ)) _).symm
      _ ≤ _ := by linarith
  calc ∑ k ∈ S, F.phiHat (τ - p.tau k) ^ 2
      ≤ ∑ k ∈ S, psiA cϱ p (τ - p.tau k) ^ 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = ∑ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2 + ∑ k ∈ Sp, psiA cϱ p (τ - p.tau k) ^ 2 :=
        (Finset.sum_filter_add_sum_filter_not S (fun k => k.1 < 0) _).symm
    _ ≤ _ := by linarith
