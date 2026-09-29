-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalCleanedSelectedHistoryEquiv_hit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-11T18:55:52.622729+00:00
-- url     : https://prove2.me/submissions/4a567db2-f029-48a7-9212-3f6607574941

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter



open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

@[simp] theorem solution
    {L : ℕ} (j : Fin L) (β : Type*) (f : Fin (L + 1) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β f).1 = f j.castSucc := by
  rfl
