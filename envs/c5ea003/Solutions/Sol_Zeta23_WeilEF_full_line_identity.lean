-- Prove2me | solution 1 for Zeta23.WeilEF.full_line_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:20:40.901272+00:00
-- url     : https://prove2.me/submissions/66774547-d869-454f-88f7-e3cfd4916bc7

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
import Definitions.Def_Zeta23_WeilEF_FullLine
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Definitions.Def_Zeta23_WeilEF_ZeroSummability
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_WeilEF_completedZeta_ne_zero_on_horizontals
import Theorems.Thm_Zeta23_WeilEF_good_heights
import Theorems.Thm_Zeta23_WeilEF_horizontal_vanish
import Theorems.Thm_Zeta23_WeilEF_integrable_Fline
import Theorems.Thm_Zeta23_WeilEF_rectangle_identity
import Theorems.Thm_Zeta23_WeilEF_verticals_eq
import Theorems.Thm_Zeta23_WeilEF_zero_sum_limit

-- from Zeta23.WeilEF.FullLine
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/FullLine.lean — the R → ∞ limit of the rectangle identity
(Zeta23.WeilEF.rectangle_identity, proved): along good heights R_j ∈ [j, j+1] the horizontal
sides vanish (‖H‖ ≪_k 1/R², ‖Λ'/Λ‖ ≪ log²j on them, reflecting Λ'/Λ(1−s) = −Λ'/Λ(s) for
re s < 1/2), the vertical sides converge to the full-line integral (dominated convergence; the
left side is folded onto the right by the functional equation and t ↦ −t), and the zero sums
over |γ| < R_j converge to the absolutely convergent tsum (EF_zero_sum_summable).  The
resulting statement is consumed by Zeta23/WeilEF/Main.lean.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set MeasureTheory
open scoped ArithmeticFunction

/-! ## Majorant pack -/

section Majorants












end Majorants

/-! ## Good heights (indexed so that no side conditions remain: R_j ∈ [j+7, j+8]) -/

section Heights


end Heights

/-! ## The vertical sides -/

section Verticals

variable {k : ℝ → ℂ}







/-- the truncated integrals converge to the full-line integral along any `R_j → ∞`. -/
theorem tendsto_interval_Fline (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) ≤ R j) :
    Tendsto (fun j : ℕ => ∫ t in (-R j)..R j, Fline k c t) atTop (𝓝 (∫ t, Fline k c t)) := by
  have hRtop : Tendsto R atTop atTop :=
    tendsto_atTop_mono hR tendsto_natCast_atTop_atTop
  exact intervalIntegral_tendsto_integral (integrable_Fline hk hkc hc1 hc2)
    (tendsto_neg_atTop_atBot.comp hRtop) hRtop

end Verticals

end WeilEF
end Zeta23
end
end

-- from Zeta23.WeilEF.FullLineAssembly
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/FullLineAssembly.lean — the R → ∞ assembly of
`full_line_identity` from: rectangle_identity (Contour), the majorant pack + heights +
vertical limits (FullLine), horizontal_vanish (Horizontal), zero_sum_limit (ZeroSumLimit).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set MeasureTheory

/-- corners of the rectangle: real and imaginary parts. -/
theorem corner_re_im (c R : ℝ) :
    ((((1 - c : ℝ) : ℂ) - R * I).re = 1 - c) ∧ ((((1 - c : ℝ) : ℂ) - R * I).im = -R) ∧
    ((((c : ℝ) : ℂ) + R * I).re = c) ∧ ((((c : ℝ) : ℂ) + R * I).im = R) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- `(1/(2πi))·(i·X) = (1/2π)·X`. -/
theorem inv_two_pi_I_mul_I (X : ℂ) :
    (1 / (2 * Real.pi * I) : ℂ) * (I * X) = (1 / (2 * Real.pi) : ℂ) * X := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp


end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Topology Filter Set MeasureTheory

theorem solution (hs : ZetaSeam) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (Hfn k ((c:ℂ) + t * I) + Hfn k (1 - c - t * I))
        * logDeriv completedRiemannZeta ((c:ℂ) + t * I)
      = (∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * Hfn k ρ)
        - Hfn k 0 - Hfn k 1 := by
  obtain ⟨Cg, hCg, R, hR⟩ := good_heights
  set f : ℂ → ℂ := fun s => Hfn k s * logDeriv completedRiemannZeta s with hf
  -- the rectangle identity at every height R_j
  have hrect : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j}) ∧
      RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
        = (∑ ρ ∈ Z, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1 := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hR j
    exact rectangle_identity hk hkc hc1 hc2 (R := R j) (by linarith)
      (completedZeta_ne_zero_on_horizontals hc1 hc2 (fun s him hr1 hr2 => (h3 s him hr1 hr2).1))
  choose Z hZ hE using hrect
  -- the three limits
  obtain ⟨hHtop, hHbot⟩ := horizontal_vanish hk hkc hc1 hc2 hCg hR
  have hZlim := zero_sum_limit hs hk hkc (R := R) (fun j => ⟨(hR j).1, (hR j).2.1⟩) hZ
  have hV := tendsto_interval_Fline hk hkc hc1 hc2 (R := R) (fun j => by linarith [(hR j).1])
  -- decomposition of the normalized rectangle integral
  have hdec : ∀ j : ℕ, RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (HIntegral f (1 - c) c (-(R j)) - HIntegral f (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, Fline k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := corner_re_im c (R j)
    rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e1, e2, e3, e4]
    have hv := verticals_eq hk hkc hc1 hc2 (R j)
    rw [hf]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, inv_two_pi_I_mul_I]
  -- LHS → (1/2π) ∫ F
  have hL : Tendsto (fun j : ℕ => RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline k c t)) := by
    have h := ((hHbot.sub hHtop).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  -- RHS → Σ' − H0 − H1
  have hRt : Tendsto (fun j : ℕ => (∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1)
      atTop (𝓝 ((∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * Hfn k ρ)
        - Hfn k 0 - Hfn k 1)) :=
    (hZlim.sub_const _).sub_const _
  have hL' : Tendsto (fun j : ℕ => (∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1)
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline k c t)) :=
    hL.congr fun j => hE j
  have := tendsto_nhds_unique hL' hRt
  exact this
