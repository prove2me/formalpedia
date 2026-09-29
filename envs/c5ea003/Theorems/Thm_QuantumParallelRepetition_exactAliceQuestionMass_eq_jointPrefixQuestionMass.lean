-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactAliceQuestionMass_eq_jointPrefixQuestionMass
-- name    : QuantumParallelRepetition.exactAliceQuestionMass_eq_jointPrefixQuestionMass
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:57:59.769568+00:00
-- url     : https://prove2.me/theorems/343bdb40-cc18-42a5-8112-c1bb8d067d51
-- title:
--   Alice's question mass equals the joint prefix question mass with her distinguished question pinned
-- statement:
--   Keep the setting above and write $\pi_n(q)=\mu^{\otimes n}(\mathbf x,\mathbf y)$ for the prior weight of a question pair $q=(\mathbf x,\mathbf y)$ under $G^{n}$. Alice's question mass at a history $h$ and a value $x\in X$ is
--   $$m_A(h,x)=\sum_{q'}\mathbf 1\big[\,c(q')=h\ \text{and}\ x'_i=x\,\big]\,\pi_n(q'),$$
--   the prior probability that the revealed history is $h$ and that Alice's question at the marked coordinate $i$ equals $x$. For masks $F_X,F_Y\subseteq\{1,\dots,n\}$ and a reference pair $q$, the joint prefix question mass is
--   $$Z(F_X,F_Y;q)=\sum_{q'}\mathbf 1\big[\,x'_j=x_j\ \forall j\in F_X\,\big]\,\mathbf 1\big[\,y'_j=y_j\ \forall j\in F_Y\,\big]\,\pi_n(q').$$
--   The theorem states that for every question pair $q$,
--   $$m_A\big(c(q),\,x_i\big)\;=\;Z\big(M_A\cup\{i\},\,M_B;\,q\big),$$
--   where $M_A$ and $M_B$ are the seed's fair masks. In words: conditioning on the revealed history together with Alice's own question at the marked coordinate is the same event as pinning Alice's questions on $M_A\cup\{i\}$ and Bob's questions on $M_B$, so the two normalising masses coincide.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L37184-L37244

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactAliceQuestionMass_eq_jointPrefixQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    exactAliceQuestionMass G n D seed
        (exactRevealCode D seed q)
        (q.1 seed.coordinate.val) =
      exactJointPrefixQuestionMass G n
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (exactFairBobQuestionMask D seed) q.1 q.2 := by sorry
