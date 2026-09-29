-- Prove2me | solution 1 for Zeta23.WeilEF.exists_far_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:34:21.896594+00:00
-- url     : https://prove2.me/submissions/155208bb-8698-49fe-8de5-d3da34b8c7f6

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
open Complex Set Filter Finset

theorem solution (S : Finset ℝ) (a : ℝ) :
    ∃ R : ℝ, a ≤ R ∧ R ≤ a + 1 ∧ ∀ y ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |R - y| := by
  classical
  set n : ℕ := S.card with hn
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδn : 2 * ((n : ℝ) + 1) * δ = 1 := by rw [hδ]; field_simp
  set cand : ℕ → ℝ := fun k => a + (2 * (k : ℝ) + 1) * δ with hcand
  by_contra hcon
  push Not at hcon
  have hbad : ∀ k ∈ Finset.range (n + 1), ∃ y ∈ S, |cand k - y| < δ := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : a ≤ cand k := by simp only [hcand]; nlinarith
    have h2 : cand k ≤ a + 1 := by
      simp only [hcand]
      have : (2 * (k : ℝ) + 1) * δ ≤ (2 * (n : ℝ) + 1) * δ := by gcongr
      nlinarith
    obtain ⟨y, hy, hlt⟩ := hcon (cand k) h1 h2
    exact ⟨y, hy, hlt⟩
  choose! f hf using hbad
  have hmaps : Set.MapsTo f (Finset.range (n + 1)) S := fun k hk => (hf k hk).1
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp [hn]) hmaps
  have h1 := (hf x hx).2
  have h2 := (hf y hy).2
  rw [hfxy] at h1
  -- |cand x − cand y| = 2|x − y|δ ≥ 2δ, but < 2δ by the triangle inequality
  have hdist : |cand x - cand y| = 2 * |(x : ℝ) - y| * δ := by
    simp only [hcand]
    rw [show a + (2 * (x:ℝ) + 1) * δ - (a + (2 * (y:ℝ) + 1) * δ) = (2 * δ) * ((x:ℝ) - y) by ring,
      abs_mul, abs_of_pos (by positivity)]
    ring
  have hxy1 : (1 : ℝ) ≤ |(x : ℝ) - y| := by
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have htri : |cand x - cand y| < 2 * δ := by
    calc |cand x - cand y| = |(cand x - f y) - (cand y - f y)| := by ring_nf
      _ ≤ |cand x - f y| + |cand y - f y| := abs_sub _ _
      _ < δ + δ := add_lt_add h1 h2
      _ = 2 * δ := by ring
  rw [hdist] at htri
  nlinarith
