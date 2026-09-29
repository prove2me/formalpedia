-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceFilterOperatorMarkerEntropy_sum_le_scalarEntropy
-- name    : QuantumParallelRepetition.exactReverseAliceFilterOperatorMarkerEntropy_sum_le_scalarEntropy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:52:49.335691+00:00
-- url     : https://prove2.me/theorems/50655e69-5b7f-40b0-b372-67f6a2d39976
-- title:
--   Total marker entropy across a side is at most the accepted scalar entropy at the first marker
-- statement:
--   Let $S$ be a strategy for $G^{n}$, let $D$ be a set of conditioned coordinates, let $s$ be a **nonempty** set of remaining coordinates, and let $\kappa$ be a side context on $s$ (an enumeration of $s$, the complementary side with its own enumeration and cut, and one ignored bit). Every marker $m\in\{0,\dots,|s|-1\}$ decodes to a forward seed $\sigma_m$ whose marked coordinate is the $m$-th element of $s$ in $\kappa$'s enumeration. Alice's marker entropy at $m$ is the accepted average
--   $$H_A(m)=\sum_{h,\,a,\,b}\mathbf 1[\text{verifier accepts on }D]\;\nu_{\sigma_m}(h)\;\Delta^{A}(\sigma_m,h,a,b),$$
--   where the sum runs over revealed histories $h$ and answer tuples $a\in A^{D}$, $b\in B^{D}$, $\nu_\sigma(h)$ is the prior mass of $h$, and
--   $$\Delta^{A}=\sum_{y}\mu_Y(y)\,\Big\langle\rho,\ \Big(\sum_{x}\Pr[x\mid y]\,f\big(A^{a}_{h}(x)\big)-f\big(\bar A^{a}_{h}(y)\big)\Big)\otimes B^{b}_{h}(y)\Big\rangle,\qquad f(z)=z\log z,$$
--   is Alice's one-step entropy increment, $\bar A^{a}_h(y)=\sum_x\Pr[x\mid y]A^{a}_h(x)$ being her mean filter and $\langle\rho,\,\cdot\otimes\cdot\rangle$ the Born pairing $\operatorname{Re}\operatorname{tr}\big(\rho\,(\cdot\otimes\cdot)\big)$. Alice's accepted scalar entropy $\Theta_A(m)$ is the same accepted average taken instead of $\sum_y\mu_Y(y)\,\eta\big(\langle\rho,\bar A^{a}_h(y)\otimes B^{b}_h(y)\rangle\big)$ with $\eta(t)=-t\log t$. The theorem states that when $|s|>0$,
--   $$\sum_{m=0}^{|s|-1}H_A(m)\;\le\;\Theta_A(0),$$
--   so the total entropy generated as the marker sweeps across the whole side is paid for by a single Shannon-type entropy of the accepted Born probabilities at the first marker.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L40058-L40079

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
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseAliceFilterOperatorMarkerEntropy_sum_le_scalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (nonempty : 0 < side.card) :
    (∑ marker : Fin side.card,
      exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker) ≤
      exactReverseAliceAcceptedScalarEntropy
        G n S D side context ⟨0, nonempty⟩ := by sorry
