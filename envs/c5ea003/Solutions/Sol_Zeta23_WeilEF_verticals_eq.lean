-- Prove2me | solution 1 for Zeta23.WeilEF.verticals_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:22:40.373917+00:00
-- url     : https://prove2.me/submissions/750fe836-e66d-46e1-bafc-08819810b375

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
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_WeilEF_continuous_logDeriv_GammaR_line
import Theorems.Thm_Zeta23_WeilEF_continuous_logDeriv_zeta_line
import Theorems.Thm_Zeta23_WeilEF_differentiableAt_GammaR
import Theorems.Thm_Zeta23_WeilEF_differentiable_paperFT
import Theorems.Thm_Zeta23_WeilEF_logDeriv_completedZeta_one_sub

-- from Zeta23.WeilEF.XiLogDeriv
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/XiLogDeriv.lean
The completed zeta function Λ = completedRiemannZeta: log-derivative decomposition, functional equation
for logDeriv, zeros in the strip = nontrivial zeros of ζ with equal analytic order.

Mathlib normalization (verified): for s ≠ 0, riemannZeta s = completedRiemannZeta s / Gammaℝ s
(riemannZeta_def_of_ne_zero) and Gammaℝ s ≠ 0 for 0 < Re s (Gammaℝ_ne_zero_of_re_pos); hence on the
open right half-plane Λ = Γℝ · ζ on the nose (completedZeta_eventuallyEq_mul) — no pole bookkeeping is
needed for the three statements below (Λ's poles at 0, 1 are excluded by hypothesis).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Filter Topology



/-- On the right half-plane, Λ = Γℝ · ζ (as germs). -/
lemma completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hΓ := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp


/-- On the right half-plane away from 1 and from the zeros of ζ:  Λ'/Λ = Γℝ'/Γℝ + ζ'/ζ. -/
theorem logDeriv_completedZeta (s : ℂ) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hstrip : 0 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hev := completedZeta_eventuallyEq_mul hstrip
  have heq : logDeriv completedRiemannZeta s = logDeriv (fun u => Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos hstrip) hζ (differentiableAt_GammaR hstrip)
    (differentiableAt_riemannZeta hs1)



end WeilEF
end Zeta23
end
end

-- from Zeta23.WeilEF.FullLine
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



/-- `H` is continuous along vertical lines (indeed paperFT k is entire). -/
theorem continuous_Hfn_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (σ : ℝ) :
    Continuous (fun t : ℝ => Hfn k ((σ : ℂ) + t * I)) := by
  have h := (differentiable_paperFT hk.continuous hkc).continuous
  unfold Hfn
  exact h.comp (by fun_prop)









end Majorants

/-! ## Good heights (indexed so that no side conditions remain: R_j ∈ [j+7, j+8]) -/

section Heights


end Heights

/-! ## The vertical sides -/

section Verticals

variable {k : ℝ → ℂ}


theorem one_sub_cast (c t : ℝ) : (1 : ℂ) - c - t * I = ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
  push_cast; ring

/-- continuity of the reflected weight `t ↦ H(1 − c − it)` (= `H((1−c) + i(−t))`). -/
theorem continuous_Hfn_reflect {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (c : ℝ) :
    Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := by
  have : (fun t : ℝ => Hfn k (1 - c - t * I))
      = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
    funext t; simp only [Function.comp_apply, one_sub_cast]
  rw [this]; exact (continuous_Hfn_line hk hkc (1 - c)).comp continuous_neg

/-- on `re = c > 1`: `Λ'/Λ = Γℝ'/Γℝ + ζ'/ζ`. -/
theorem logDeriv_completedZeta_line {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    logDeriv completedRiemannZeta ((c : ℂ) + t * I)
      = logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) + logDeriv riemannZeta ((c : ℂ) + t * I) := by
  have hre : ((c : ℂ) + t * I).re = c := by simp
  refine logDeriv_completedZeta _ ?_ ?_ (by rw [hre]; linarith)
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · exact riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hc1)




end Verticals

end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Topology Filter Set MeasureTheory
open scoped ArithmeticFunction
variable {k : ℝ → ℂ}

theorem solution (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) (R : ℝ) :
    VIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s) c (-R) R
      - VIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, Fline k c t := by
  
  set L := logDeriv completedRiemannZeta with hL
  have hLc : Continuous (fun t : ℝ => L ((c : ℂ) + t * I)) := by
    have : (fun t : ℝ => L ((c:ℂ) + t * I)) = fun t : ℝ => logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)
        + logDeriv riemannZeta ((c : ℂ) + t * I) := funext (logDeriv_completedZeta_line hc1)
    rw [this]
    exact (continuous_logDeriv_GammaR_line (by linarith) hc2).add (continuous_logDeriv_zeta_line hc1)
  have hHc := continuous_Hfn_line hk hkc c
  have hH2 : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := continuous_Hfn_reflect hk hkc c
  -- the left-line integrand, pointwise
  have hleft : ∀ y : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I)
      = -(Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) * L ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    have h0 : (c : ℂ) + ((-y:ℝ):ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : (c : ℂ) + ((-y:ℝ):ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [hs, hL, logDeriv_completedZeta_one_sub _ h0 h1]
    have : (1:ℂ) - ((c : ℂ) + ((-y:ℝ):ℂ) * I) = 1 - c - ((-y : ℝ) : ℂ) * I := by ring
    rw [this]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hH2.mul hLc).intervalIntegrable _ _
  have hfold : (∫ y in (-R)..R, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  rw [hfold, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Fline]
  ring
