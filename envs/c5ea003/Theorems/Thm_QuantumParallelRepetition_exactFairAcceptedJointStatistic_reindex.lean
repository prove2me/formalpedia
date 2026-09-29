-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFairAcceptedJointStatistic_reindex
-- name    : QuantumParallelRepetition.exactFairAcceptedJointStatistic_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:40:00.896446+00:00
-- url     : https://prove2.me/theorems/c0abf427-9f6c-4225-9d8d-15ab22e63cfc
-- title:
--   Reindexing an accepted joint statistic from revealed histories to full question tuples
-- statement:
--   Fix a game $G$, a repetition count $n$, a coordinate set $D\subseteq\{1,\dots,n\}$, and a sampling seed for the coordinates outside $D$, with distinguished coordinate $i$. Let $f(h,a,b,x,y)$ be an arbitrary real-valued function of a revealed history $h$, answer tuples $a\in A^{D}$ and $b\in B^{D}$, and a question pair $(x,y)\in X\times Y$. Then
--   $$\sum_{h}\sum_{a}\sum_{b}\mathbf{1}[\text{accept}(h,a,b)]\;m(h)\sum_{x,y}\mu(x,y)\,f(h,a,b,x,y)\;=\;\sum_{q}\pi_n(q)\sum_{a}\sum_{b}\mathbf{1}[\text{accept}(c(q),a,b)]\;f\big(c(q),a,b,q_X(i),q_Y(i)\big),$$
--   where $m(h)$ is the mass of the revealed history $h$, $q=(q_X,q_Y)\in X^{n}\times Y^{n}$ ranges over full question tuples with weight $\pi_n(q)$ under $G^{n}$, $c(q)$ is the history that $q$ reveals for the given seed, and "accept" means the verifier accepts in every coordinate of $D$. Thus averaging an acceptance-gated statistic over revealed histories together with an independently drawn question pair is the same as averaging it over full question tuples, evaluated at the questions the tuple assigns to the distinguished coordinate.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L37918-L38028

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
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
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactFairAcceptedJointStatistic_reindex
    (G : Game X Y A B) (n : ℕ) (_ : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (f : ExactRevealHistory X Y D seed →
      ({j : Fin n // j ∈ D} → A) →
      ({j : Fin n // j ∈ D} → B) → X → Y → ℝ) :
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            (∑ x : X, ∑ y : Y,
              G.questionWeight x y *
                f history aliceAnswer bobAnswer x y)
        else 0) =
      ∑ q : ExactFullQuestion X Y n,
        exactPriorQuestionWeight G n q *
          (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
           ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
            if exactHistoryAccepted G n D
              ⟨seed, exactRevealCode D seed q,
                aliceAnswer, bobAnswer⟩ then
              f (exactRevealCode D seed q)
                aliceAnswer bobAnswer
                (q.1 seed.coordinate.val)
                (q.2 seed.coordinate.val)
            else 0) := by sorry
