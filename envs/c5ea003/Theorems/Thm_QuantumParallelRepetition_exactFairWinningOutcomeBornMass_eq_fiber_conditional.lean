-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFairWinningOutcomeBornMass_eq_fiber_conditional
-- name    : QuantumParallelRepetition.exactFairWinningOutcomeBornMass_eq_fiber_conditional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T13:19:38.1205+00:00
-- url     : https://prove2.me/theorems/6c320334-0695-4f6f-b4c1-4d24f6899bdb
-- title:
--   The fair winning Born mass factors as fiber question mass times joint conditional winning mass
-- statement:
--   Let $r$ be a history flag and $(x,y)$ a question pair whose fiber question mass $M(r,x,y)$ — the total $\mu^{\otimes n}$-weight of full question tuples $(x_\bullet, y_\bullet)$ compatible with $r$'s revealed history and asking $x,y$ at the distinguished coordinate — is nonzero. Then
--   $$\text{fair winning outcome Born mass of } r \text{ at } (x,y) \;=\; M(r,x,y)\cdot \sum_{a,b} [V(x,y,a,b)]\,\mathrm{Re}\,\mathrm{tr}\!\big(\rho\,(F^{x,y}_a \otimes G^{x,y}_b)\big),$$
--   the second factor being the joint conditional winning mass of $r$ at $(x,y)$. Thus the unnormalised Born weight of the winning outcomes with this history and this question pair splits into a purely classical question-fiber factor and a conditional quantum winning probability.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L52397-L52483

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactFairWinningOutcomeBornMass_eq_fiber_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D history.seed history.history x y ≠ 0) :
    exactFairWinningOutcomeBornMass G n S D history x y =
      exactFiberQuestionMass
          G n D history.seed history.history x y *
        exactJointConditionalWinningMass
          G n S D history.seed history.history
          history.aliceAnswer history.bobAnswer x y := by sorry
