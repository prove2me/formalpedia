-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperR8UniformRank
-- name    : ErdosProblems_Erdos269_PaperR8UniformRank
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:13:11.260904+00:00
-- url     : https://prove2.me/theorems/8b6d5da9-5067-409a-a4d4-303c21572a91
-- title:
--   PaperR8UniformRank
-- statement:
--   Defines bounded real columns and matrices, finite separated rank, the subtype of finite-rank matrices, and extended-real uniform error as the supremum of pointwise absolute errors.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR8UniformRank.lean#L1-L355
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7AnalyticInterfaces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# The infinite uniform finite-rank obstruction

The finite staircase minors alone do not prove a uniform lower bound. This
file uses their column separation inside a finite-dimensional bounded column
space, and a finite covering of a compact ball. Row factors in an arbitrary
separated representation need not be bounded; the subspace is formed by
intersecting their algebraic span with the space of bounded functions.

The final infimum ranges over ALL finite-separated-rank matrices. It uses an
extended nonnegative supremum so that unbounded approximants have infinite
uniform error, never the spurious zero returned by an unbounded real iSup.
The resulting finite value is also identified after conversion to the reals.
All proof text is an uncompiled candidate against the packet's pinned Mathlib.
-/

namespace ErdosProblems.Erdos269.PaperR8

open PaperR7 ErdosProblems.Shared Set Metric
open scoped BigOperators Topology BoundedContinuousFunction ENNReal

abbrev BoundedColumn := ℕ →ᵇ ℝ


def FiniteSeparatedRank (A : ℕ → ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ f g : Fin d → ℕ → ℝ,
    ∀ i j, A i j = ∑ k : Fin d, f k i * g k j












/-- All finite-separated-rank matrices, with no bounded-factor restriction. -/
abbrev FiniteRankMatrix := {A : ℕ → ℕ → ℝ // FiniteSeparatedRank A}

/-- An extended supremum is essential: the real supremum convention at an
unbounded set must not turn infinite error into zero. -/
noncomputable def uniformError (C A : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ j : ℕ, ENNReal.ofReal |C i j - A i j|







end ErdosProblems.Erdos269.PaperR8


