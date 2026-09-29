-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobFilterOperatorMarkerEntropy_sum_le_scalarEntropy
-- name    : QuantumParallelRepetition.exactReverseBobFilterOperatorMarkerEntropy_sum_le_scalarEntropy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:37:33.545643+00:00
-- url     : https://prove2.me/theorems/9121fbb6-2fa7-49f9-ae5f-c32f482dd698
-- title:
--   Bob's total marker entropy is bounded by the accepted scalar entropy at the initial marker
-- statement:
--   Fix a strategy $S$ for $G^{n}$ with shared state $\rho$, a coordinate set $D$, a nonempty set $\mathrm{side}$ of coordinates outside $D$, and an ordering context on $\mathrm{side}$. Let $E^{B}(m)$ be Bob's filter operator marker entropy at marker $m$, and let $H^{B}(0)$ be Bob's accepted scalar entropy at the initial marker: for the seed decoded from marker $0$, the sum over revealed histories and answer tuples, gated by acceptance on all of $D$, of the reveal mass times
--   $$\sum_{x\in X}\mu_X(x)\,\eta\Big(\big\langle\rho,\;A^{a}_{h}(x)\otimes\bar B^{b}_{h}(x)\big\rangle\Big),\qquad \eta(t)=-t\log t,$$
--   where $\mu_X$ is the marginal question distribution on $X$, $A$ is Alice's question filter and $\bar B$ is Bob's mean filter. The theorem asserts
--   $$\sum_{m}E^{B}(m)\;\le\;H^{B}(0),$$
--   so the entire operator-entropy budget accumulated along the prefix filtration is dominated by a single classical entropy of Born probabilities.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L40177-L40212

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseBobFilterOperatorMarkerEntropy_sum_le_scalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (sideNonempty : 0 < side.card) :
    (∑ marker : Fin side.card,
      exactReverseBobFilterOperatorMarkerEntropy
        G n S D side context marker) ≤
      exactReverseBobAcceptedScalarEntropy
        G n S D side context ⟨0, sideNonempty⟩ := by sorry
