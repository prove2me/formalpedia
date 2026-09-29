-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceFilterOperatorMarkerEntropy_sum_telescope
-- name    : QuantumParallelRepetition.exactReverseAliceFilterOperatorMarkerEntropy_sum_telescope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:29:27.790378+00:00
-- url     : https://prove2.me/theorems/ddd9bdfd-5815-49aa-a66c-27f56130f9c5
-- title:
--   Alice's marker entropies telescope to a difference of aligned prefix potentials
-- statement:
--   Fix a game $G$, a repetition count $n$, a strategy $S$ for $G^{n}$, a coordinate set $D$, a set $\mathrm{side}$ of coordinates outside $D$, and an ordering context on $\mathrm{side}$. For each marker $m\in\{0,\dots,\lvert\mathrm{side}\rvert-1\}$, Alice's filter operator marker entropy $E^{A}(m)$ is obtained from the seed decoded from $m$ by summing, over revealed histories and both players' answers on $D$, the reveal mass times Alice's history entropy increment, gated by acceptance in every coordinate of $D$. Writing $\Phi^{A}(k)$ for Alice's aligned continuous-functional-calculus prefix potential at level $k$, the theorem asserts
--   $$\sum_{m}E^{A}(m)=\Phi^{A}\big(\lvert\mathrm{side}\rvert\big)-\Phi^{A}(0).$$
--   Thus the marker entropies are precisely the one-step increments of a single potential along the prefix filtration, so their total collapses to the difference between the terminal and initial values of that potential.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L39636-L39673

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseAliceFilterOperatorMarkerEntropy_sum_telescope
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side) :
    (∑ marker : Fin side.card,
      exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker) =
      exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context side.card -
        exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context 0 := by sorry
