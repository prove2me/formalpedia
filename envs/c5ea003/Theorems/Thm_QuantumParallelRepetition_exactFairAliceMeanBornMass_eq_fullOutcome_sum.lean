-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFairAliceMeanBornMass_eq_fullOutcome_sum
-- name    : QuantumParallelRepetition.exactFairAliceMeanBornMass_eq_fullOutcome_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T05:41:40.043637+00:00
-- url     : https://prove2.me/theorems/89967bdc-efd4-4296-807c-e4b501ba9477
-- title:
--   Alice's mean-filter Born mass equals the total full-outcome mass of a record
-- statement:
--   Fix a game $G$ with question distribution $\mu$ and $Y$-marginal $\mu_Y$, a repetition count $n$, a strategy $S$ for $G^{n}$ with shared state $\rho$, and a coordinate set $D$. Let $r$ be a record consisting of a seed, a revealed history $h$, Alice answers $a\in A^{D}$ and Bob answers $b\in B^{D}$, and write $i$ for the distinguished coordinate of its seed. Then
--   $$m(h)\sum_{y\in Y}\mu_Y(y)\,\Big\langle\rho,\;\bar A^{a}_{h}(y)\otimes B^{b}_{h}(y)\Big\rangle=\sum_{x\in X}\sum_{y\in Y}W_r(x,y),$$
--   where $m(h)$ is the reveal mass of $h$, $\bar A$ is Alice's mean filter, $B$ is Bob's question filter, $\langle\rho,\,\cdot\otimes\cdot\rangle$ is the Born pairing, and $W_r(x,y)$ is the total probability, under the outcome law of $S$ in $G^{n}$, of the outcomes whose locally sampleable code is the tuple $(i,x,y,r)$. In other words, replacing Alice's question filter by its average against the conditional distribution of her question loses no probability mass: the resulting Born expectation still sums to the full-outcome mass of the record.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L40285-L40343

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
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
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactFairAliceMeanBornMass_eq_fullOutcome_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactRevealMass G n D r.seed r.history *
        (∑ y : Y, G.marginalY y *
          bornTracePairing S.state.matrix
            (exactAliceMeanFilter
              G n S D r.seed r.history r.aliceAnswer y)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y)) =
      ∑ x : X, ∑ y : Y,
        exactFairFullOutcomeBornMass G n S D r x y := by sorry
