-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactBobConditionalMatrix_eq_joint
-- name    : QuantumParallelRepetition.exactBobConditionalMatrix_eq_joint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T02:49:54.903896+00:00
-- url     : https://prove2.me/theorems/b8b39bc7-a7ef-470d-956f-132551a93d3d
-- title:
--   Bob's conditional operator average equals the Bob marginal of the joint fiber
-- statement:
--   In the setting of the previous lemma — a finite game $G$, its $n$-fold repetition with question distribution $\mu_n$ on $X^n \times Y^n$, a conditioned set $D \subseteq [n]$, a seed $\sigma$ with distinguished remaining coordinate $i$, and a fixed revealed history $h = \rho_\sigma(\mathbf{x},\mathbf{y})$ — put
--   $$\beta_h(y) = \sum_{\rho_\sigma(\mathbf{x},\mathbf{y}) = h,\ \mathbf{y}_i = y} \mu_n(\mathbf{x},\mathbf{y}),$$
--   and let $w_{x,y}$, its Bob marginal $b_{x,y}(\mathbf{y}) = \sum_{\mathbf{x}} w_{x,y}(\mathbf{x},\mathbf{y})$, and its total mass $Z_{x,y}$ be as before. The theorem asserts that if $Z_{x,y} \neq 0$, then for every family of $d \times d$ complex matrices $E(\mathbf{y})$ indexed by $\mathbf{y} \in Y^n$,
--   $$\sum_{\rho_\sigma(\mathbf{x},\mathbf{y}) = h,\ \mathbf{y}_i = y} \frac{\mu_n(\mathbf{x},\mathbf{y})}{\beta_h(y)}\, E(\mathbf{y}) \;=\; \sum_{\mathbf{y} \in Y^n} \frac{b_{x,y}(\mathbf{y})}{Z_{x,y}}\, E(\mathbf{y}).$$
--   Thus the operator Bob forms by averaging $E$ against his posterior on question tuples given $(h,y)$, which does not refer to Alice's question $x$, coincides with the average against the Bob marginal of the two-sided fiber distribution attached to $(x,y)$. This is the exact mirror of the corresponding statement for Alice.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L28423-L28504

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
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
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactBobConditionalMatrix_eq_joint
    {d : Type*} [Fintype d]
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0)
    (E : (Fin n → Y) → Matrix d d ℂ) :
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.2 seed.coordinate.val = y
      then
        (exactPriorQuestionWeight G n q /
          exactBobQuestionMass
            G n D seed history y) • E q.2
      else 0) =
      ∑ ys : Fin n → Y,
        (exactFiberBobMarginal
          G n D seed history x y ys /
          exactFiberQuestionMass
            G n D seed history x y) • E ys := by sorry
