-- Prove2me | solution 1 for Zeta23.WeilEF.integrable_Fline
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:24:51.119629+00:00
-- url     : https://prove2.me/submissions/8ebfacb0-1d08-4e54-bf88-04377f35df9d

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
import Theorems.Thm_Zeta23_WeilEF_continuous_logDeriv_zeta_line
import Theorems.Thm_Zeta23_WeilEF_differentiableAt_GammaR
import Theorems.Thm_Zeta23_WeilEF_differentiable_paperFT
import Theorems.Thm_Zeta23_WeilEF_integrable_mul_logDeriv_GammaR_of_decay
import Theorems.Thm_Zeta23_WeilEF_norm_Hfn_le
import Theorems.Thm_Zeta23_WeilEF_norm_logDeriv_zeta_le_of_one_lt_re

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



/-- generic: a continuous `φ` with `‖φ(t)‖ ≤ C/(1+t²)` times `ζ'/ζ(c+it)` is integrable. -/
theorem integrable_mul_logDeriv_zeta_of_decay {φ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) {c : ℝ} (hc1 : 1 < c) :
    Integrable (fun t : ℝ => φ t * logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_zeta_le_of_one_lt_re hc1
  have hC0 : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hφ 0); simpa using this
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C * M)))
    (hφc.mul (continuous_logDeriv_zeta_line hc1)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖φ t‖ * ‖logDeriv riemannZeta ((c : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * M := mul_le_mul (hφ t) (hM t) (norm_nonneg _) (by positivity)
    _ = C * M * (1 + t ^ 2)⁻¹ := by ring






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
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) : Integrable (Fline k c) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  set φ : ℝ → ℂ := fun t => Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I) with hφ
  have hφc : Continuous φ := (continuous_Hfn_line hk hkc c).add (continuous_Hfn_reflect hk hkc c)
  have hφb : ∀ t, ‖φ t‖ ≤ (2 * C) / (1 + t ^ 2) := by
    intro t
    have h1 := hC c t (by linarith) (by linarith)
    have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
    rw [← one_sub_cast] at h2
    rw [neg_sq] at h2
    calc ‖φ t‖ ≤ ‖Hfn k ((c : ℂ) + t * I)‖ + ‖Hfn k (1 - c - t * I)‖ := norm_add_le _ _
      _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add h1 h2
      _ = (2 * C) / (1 + t ^ 2) := by ring
  have hΓ := integrable_mul_logDeriv_GammaR_of_decay hφc (by positivity) hφb
    (by linarith : (1:ℝ) / 2 ≤ c) hc2
  have hζ := integrable_mul_logDeriv_zeta_of_decay hφc hφb hc1
  refine (hΓ.add hζ).congr (Eventually.of_forall fun t => ?_)
  simp only [Fline, hφ, logDeriv_completedZeta_line hc1 t, Pi.add_apply]
  ring
