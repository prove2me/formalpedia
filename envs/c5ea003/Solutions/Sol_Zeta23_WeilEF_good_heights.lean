-- Prove2me | solution 1 for Zeta23.WeilEF.good_heights
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:33:12.726735+00:00
-- url     : https://prove2.me/submissions/97c42401-331f-43e9-8065-f6f5e7f3d739

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
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
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
import Definitions.Def_Zeta23_ZetaReflect
import Theorems.Thm_Zeta23_WeilEF_good_heights_at

-- from Zeta23.WeilEF.GoodHeights
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/GoodHeights.lean — good horizontal heights for the EF contour: for every j ≥ 7 a height
R ∈ [j, j+1] avoiding the ordinates of all ζ-zeros near heights ±j by ≥ 1/(2(n+1)) (n ≪ log j of them;
pigeonhole over n+1 cell midpoints), whence on Im s = ±R, 1/2 ≤ Re s ≤ 2:  ζ(s) ≠ 0 and
‖ζ'/ζ(s)‖ ≤ C log²(j+3), by the partial fraction Zeta23.WeilEF.zeta_logDeriv_partial_fraction (with its
multiplicity-sum conjunct) and the proved local zero count Zeta23.RvM.zetaZeroConfig_local_count
(via Zeta23.Tail.LocalCount).  Statement shape (consumed by Contour.lean horizontal_vanish):
j ≥ 7, σ ∈ [1/2, 2], bound in log((j:ℝ)+3).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set Filter Finset

/-! ### Gap / pigeonhole lemma -/


/-! ### Elementary facts used below -/






/-! ### good heights -/




end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Set Filter Finset

theorem solution : ∃ Cg : ℝ, 0 < Cg ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
    (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
    ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := good_heights_at
  have hex : ∀ j : ℕ, ∃ R : ℝ, ((j + 7 : ℕ) : ℝ) ≤ R ∧ R ≤ ((j + 7 : ℕ) : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C * (Real.log (((j + 7 : ℕ) : ℝ) + 3)) ^ 2 :=
    fun j => h (j + 7) (by omega)
  refine ⟨C, hC, fun j => (hex j).choose, fun j => ?_⟩
  dsimp only
  obtain ⟨hs1, hs2, hs3⟩ := (hex j).choose_spec
  have e : ((j + 7 : ℕ) : ℝ) = (j : ℝ) + 7 := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · calc (j : ℝ) + 7 = ((j + 7 : ℕ) : ℝ) := e.symm
      _ ≤ _ := hs1
  · exact hs2.trans (by rw [e]; linarith)
  · intro s him h1 h2
    have e3 : Real.log (((j + 7 : ℕ) : ℝ) + 3) = Real.log ((j : ℝ) + 10) := by rw [e]; ring_nf
    obtain ⟨h3, h4⟩ := hs3 s him h1 h2
    exact ⟨h3, by rwa [e3] at h4⟩
