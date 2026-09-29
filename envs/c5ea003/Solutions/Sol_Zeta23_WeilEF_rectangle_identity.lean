-- Prove2me | solution 1 for Zeta23.WeilEF.rectangle_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:23:45.291503+00:00
-- url     : https://prove2.me/submissions/dc99ab2e-bf87-4e52-9f7a-4e273b38b931

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_Analytic_rectangleIntegralPrime_mul_logDeriv_of_poles
import Theorems.Thm_Zeta23_WeilEF_differentiable_paperFT

-- from Zeta23.FromPNTPlus.Rectangle
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Rectangle.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
@[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl














lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩





lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

















end

-- from Zeta23.RvM.CountByIntegral
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/CountByIntegral.lean — the zero count as a contour integral, specialised to Λ.
Used by Zeta23/RvM/Statement.lean and MainTerm.lean (the symmetry fold and the Γ-side).

MAIN RESULT `rectangleIntegral'_logDeriv_completedZeta_eq_Ncount`: for 0 < T₁ ≤ T₂, neither the
ordinate of a nontrivial zero,
    (1/2πi) ∮_{∂([−1,2]×[T₁,T₂])} Λ'/Λ(s) ds = N(T₁,T₂)        (Λ = completedRiemannZeta),
where N = Zeta23.Ncount counts nontrivial zeros of Mathlib's riemannZeta with T₁ < γ ≤ T₂ with
multiplicity zeroMult = analyticOrderAt ζ. Ingredients (all proved here from Mathlib):
 • Λ is analytic off {0,1}; Λ = Gammaℝ·ζ with Gammaℝ ≠ 0 on Re s > 0, so on the strip the zeros
   and their analytic orders agree with ζ's; Λ ≠ 0 for Re s ≥ 1 (Mathlib's non-vanishing of ζ)
   and, by Λ(1−s) = Λ(s), for Re s ≤ 0; hence {Λ = 0} = nontrivial zeros of ζ exactly.
 • Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (weighted argument principle, g ≡ 1).
-/

open Complex Set Topology Filter Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Λ = completedRiemannZeta: analyticity, relation to ζ, zeros -/

lemma analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ completedRiemannZeta (({0, 1} : Set ℂ)ᶜ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds (by simp [h0, h1]))

lemma completedRiemannZeta_eq_Gammaℝ_mul {s : ℂ} (hs : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

lemma completedRiemannZeta_eq_zero_iff_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [completedRiemannZeta_eq_Gammaℝ_mul h0 hG, mul_eq_zero]
  simp [hG]

lemma completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  rw [Ne, completedRiemannZeta_eq_zero_iff_of_re_pos (by linarith)]
  exact riemannZeta_ne_zero_of_one_le_re hs

lemma completedRiemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  exact completedRiemannZeta_ne_zero_of_one_le_re (by simp; linarith)


/-- On the open right half-plane (away from 1) the analytic order of Λ equals zeroMult = the
analytic order of ζ. -/
lemma analyticOrderNatAt_completedRiemannZeta {ρ : ℂ} (h : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderNatAt completedRiemannZeta ρ = zeroMult ρ := by
  have h0 : ρ ≠ 0 := fun h' => by simp [h'] at h
  have hev : riemannZeta =ᶠ[𝓝 ρ] (completedRiemannZeta * fun s => (Gammaℝ s)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
    rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  have hΛ := analyticAt_completedRiemannZeta h0 h1
  have hGinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
  have hG0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 :=
    hGinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h))
  unfold zeroMult analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hΛ hGinv, hG0, add_zero]

/-! ## The count -/


end RvM
end Zeta23
end
end

-- from Zeta23.WeilEF.Contour
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Contour.lean — The main contour: rectangle identity for H·Λ'/Λ,
horizontal vanishing along good heights, and the R → ∞ full-line identity.
Consumes: Zeta23.Analytic.rectangleIntegral'_mul_logDeriv_of_poles,
Zeta23.WeilEF.GoodHeights, differentiable_paperFT,
XiLogDeriv zeros/poles data, Mathlib completedRiemannZeta_residue_one /
completedHurwitzZetaEven_residue_zero.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set


/- `full_line_identity` (the R → ∞ limit) lives in Zeta23/WeilEF/FullLine.lean,
which imports this file. -/

end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Topology Filter Set

theorem solution {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {R : ℝ} (hR : 7 ≤ R)
    (hgood : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c →
      completedRiemannZeta s ≠ 0) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      RectangleIntegral' (fun s => Hfn k s * logDeriv completedRiemannZeta s)
          ((1 - c : ℝ) - R * I) ((c : ℝ) + R * I)
        = (∑ ρ ∈ Z, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1 := by
  classical
  set z : ℂ := (1 - c : ℝ) - R * I with hzdef
  set w : ℂ := (c : ℝ) + R * I with hwdef
  have hzre : z.re = 1 - c := by simp [hzdef]
  have hzim : z.im = -R := by simp [hzdef]
  have hwre : w.re = c := by simp [hwdef]
  have hwim : w.im = R := by simp [hwdef]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have him : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (-R ≤ s.im ∧ s.im ≤ R) := by
    intro s
    simp only [Rectangle, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIcc_of_le (show (1 - c : ℝ) ≤ c by linarith),
      Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]
  set P : Finset ℂ := {0, 1} with hPdef
  have hfin := zetaSeam.finite_window (-R) R
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmemiff : ∀ ρ : ℂ, ρ ∈ Z ↔ (IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im ≤ R) := by
    intro ρ
    rw [hZdef, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
  have hZcoe : (Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im < R} := by
    ext ρ
    rw [Finset.mem_coe, hZmemiff]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, lt_of_le_of_ne h3 ?_⟩
      intro h
      exact hgood ρ (Or.inl h) (by linarith [h1.2.1]) (by linarith [h1.2.2])
        ((Zeta23.RvM.completedRiemannZeta_eq_zero_iff_of_re_pos h1.2.1).mpr h1.1)
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.le⟩
  refine ⟨Z, hZcoe, ?_⟩
  have hZP : Disjoint Z P := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρP
    have h1 := ((hZmemiff ρ).mp hρ).1
    rw [hPdef] at hρP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρP
    rcases hρP with rfl | rfl
    · have h2 := h1.2.1
      rw [Complex.zero_re] at h2
      exact lt_irrefl _ h2
    · have h2 := h1.2.2
      rw [Complex.one_re] at h2
      exact lt_irrefl _ h2
  have hPint : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him,
      hzre, hzim, hwre, hwim]
    rw [hPdef] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · constructor
      · simp only [Complex.zero_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.zero_im, Set.mem_Ioo]
        constructor <;> linarith
    · constructor
      · simp only [Complex.one_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.one_im, Set.mem_Ioo]
        constructor <;> linarith
  have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w \ (P : Set ℂ)) := by
    rintro s ⟨_, hsP⟩
    rw [hPdef] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    exact Zeta23.RvM.analyticAt_completedRiemannZeta hsP.1 hsP.2
  have hg : AnalyticOnNhd ℂ (Hfn k) (Rectangle z w) := by
    intro s _
    have hdiff : Differentiable ℂ (Hfn k) := by
      unfold Hfn
      exact (differentiable_paperFT hk.continuous hkc).comp
        ((differentiable_id.sub_const _).div_const _)
    exact hdiff.analyticAt s
  have hborder : ∀ s ∈ RectangleBorder z w, completedRiemannZeta s ≠ 0 := by
    intro s hs h0
    have hsrect := rectangleBorder_subset_rectangle z w hs
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      hzre, hzim, hwre, hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood s (Or.inr h') hr1 hr2 h0
    · exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_re_nonpos (by rw [h']; linarith) h0
    · exact hgood s (Or.inl h') hr1 hr2 h0
    · exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_one_le_re (by rw [h']; linarith) h0
  have hZchar : ∀ s ∈ Rectangle z w \ (P : Set ℂ), (completedRiemannZeta s = 0 ↔ s ∈ Z) := by
    rintro s ⟨hsrect, hsP⟩
    rw [hPdef] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    rw [hZmemiff]
    constructor
    · intro h0
      have hrepos : 0 < s.re := by
        by_contra hle
        exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_re_nonpos (by linarith) h0
      have hrelt : s.re < 1 := by
        by_contra hge
        exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_one_le_re (by linarith) h0
      have hnz : IsNontrivialZero s :=
        ⟨(Zeta23.RvM.completedRiemannZeta_eq_zero_iff_of_re_pos hrepos).mp h0, hrepos, hrelt⟩
      refine ⟨hnz, ?_, hi2⟩
      rcases lt_or_eq_of_le hi1 with h | h
      · exact h
      · exact absurd h0 (hgood s (Or.inr h.symm) hr1 hr2)
    · rintro ⟨h1, _, _⟩
      exact (Zeta23.RvM.completedRiemannZeta_eq_zero_iff_of_re_pos h1.2.1).mpr h1.1
  have hZsub : (Z : Set ℂ) ⊆ Rectangle z w := by
    intro ρ hρ
    rw [Finset.mem_coe, hZmemiff] at hρ
    obtain ⟨h1, h2, h3⟩ := hρ
    exact (hmem ρ).mpr ⟨⟨by linarith [h1.2.1], by linarith [h1.2.2]⟩, h2.le, h3⟩
  have hpole : ∀ p ∈ P, ∃ cp : ℂ, cp ≠ 0 ∧
      Filter.Tendsto (fun s => (s - p) ^ (1 : ℕ) * completedRiemannZeta s)
        (nhdsWithin p {p}ᶜ) (nhds cp) := by
    intro p hp
    rw [hPdef] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨-1, by norm_num, ?_⟩
      have h := HurwitzZeta.completedHurwitzZetaEven_residue_zero (0 : UnitAddCircle)
      norm_num at h
      refine h.congr (fun s => ?_)
      simp [completedRiemannZeta]
    · refine ⟨1, one_ne_zero, ?_⟩
      refine completedRiemannZeta_residue_one.congr (fun s => ?_)
      simp
  have key := Zeta23.Analytic.rectangleIntegralPrime_mul_logDeriv_of_poles hre him Z P hZP hPint hf hg
    hborder hZchar hZsub (fun _ => 1) hpole
  rw [key]
  have hord : ∀ ρ ∈ Z, (analyticOrderNatAt completedRiemannZeta ρ : ℂ) = (zeroMult ρ : ℂ) := by
    intro ρ hρ
    have h1 := ((hZmemiff ρ).mp hρ).1
    rw [Zeta23.RvM.analyticOrderNatAt_completedRiemannZeta h1.2.1
      (fun h' => by
        have h2 := h1.2.2
        rw [h', Complex.one_re] at h2
        exact lt_irrefl _ h2)]
  have hPsum : ∑ p ∈ P, ((1 : ℕ) : ℂ) * Hfn k p = Hfn k 0 + Hfn k 1 := by
    rw [hPdef, Finset.sum_insert (by simp), Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl (fun ρ hρ => by rw [hord ρ hρ]), hPsum]
  ring
