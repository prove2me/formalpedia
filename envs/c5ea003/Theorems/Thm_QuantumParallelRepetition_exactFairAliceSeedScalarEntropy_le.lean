-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFairAliceSeedScalarEntropy_le
-- name    : QuantumParallelRepetition.exactFairAliceSeedScalarEntropy_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:29:52.146522+00:00
-- url     : https://prove2.me/theorems/c5d3c91c-fe28-4365-b11a-df11eb7f9a7e
-- title:
--   Counting bound for Alice's accepted scalar entropy at a fixed seed
-- statement:
--   Fix a game $G$ with $Y$-marginal $\mu_Y$, a strategy $S$ for $G^{n}$ with shared state $\rho$, and a coordinate set $D$ whose postselection mass $p_D$ is strictly positive; fix also a seed for the coordinates outside $D$. Alice's seed scalar entropy is
--   $$H^{A}=\sum_{h}\sum_{a}\sum_{b}\mathbf{1}[\text{accept}]\;m(h)\sum_{y\in Y}\mu_Y(y)\,\eta\Big(\big\langle\rho,\;\bar A^{a}_{h}(y)\otimes B^{b}_{h}(y)\big\rangle\Big),\qquad\eta(t)=-t\log t,$$
--   the sum running over revealed histories $h$ and answer tuples $a\in A^{D}$, $b\in B^{D}$ with $m(h)$ the reveal mass, $\bar A$ Alice's mean filter and $B$ Bob's question filter. The theorem asserts the counting bound
--   $$H^{A}\le p_D\,\log\!\Big(\frac{N_D}{p_D}\Big),\qquad N_D=\lvert A\rvert^{\lvert D\rvert}\,\lvert B\rvert^{\lvert D\rvert},$$
--   with $N_D$ the number of pairs of answer tuples on $D$. So the entropy of the postselected answer statistics at a single seed obeys the usual $p\log(N/p)$ estimate.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L40922-L40962

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactFairAliceSeedScalarEntropy_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (seed : ExactRemainingSeed D) :
    exactFairAliceSeedScalarEntropy G n S D seed ≤
      repeatedPostselectionMass G n S D *
        Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) := by sorry
