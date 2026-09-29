-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactRevealCode_eq_iff_fair_question_masks
-- name    : QuantumParallelRepetition.exactRevealCode_eq_iff_fair_question_masks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:42:36.926112+00:00
-- url     : https://prove2.me/theorems/869679c0-6e26-4d4c-b4f5-31b745096df7
-- title:
--   The revealed history is precisely the restriction of the questions to the two fair masks
-- statement:
--   Fix $n$, a set $D\subseteq\{1,\dots,n\}$ of already-conditioned coordinates, and a seed $\sigma$ on the remaining coordinates, with marked coordinate $i$, blocks $L$ and $R$, and prefixes $L_{<\ell}$ and $R_{<r}$. For a full question pair $q=(\mathbf x,\mathbf y)\in X^{n}\times Y^{n}$ the *revealed history* $c(q)$ records six restrictions: $\mathbf x$ and $\mathbf y$ on $D$, $\mathbf x$ on $L$, $\mathbf y$ on $R$, $\mathbf y$ on $L_{<\ell}$, and $\mathbf x$ on $R_{<r}$. Define the fair question masks
--   $$M_A=D\cup L\cup R_{<r},\qquad M_B=D\cup R\cup L_{<\ell},$$
--   the coordinates on which the history reveals Alice's, respectively Bob's, question. The theorem states that for all question pairs $q,q'$,
--   $$c(q')=c(q)\iff \big(x'_j=x_j\ \text{for all }j\in M_A\big)\ \text{and}\ \big(y'_j=y_j\ \text{for all }j\in M_B\big).$$
--   Thus the fibres of the reveal code are exactly the sets of question pairs that agree with a given pair on $M_A$ on Alice's side and on $M_B$ on Bob's side; the history carries neither more nor less information than those two restrictions.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L37092-L37182

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
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

theorem QuantumParallelRepetition.exactRevealCode_eq_iff_fair_question_masks
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q q' : ExactFullQuestion X Y n) :
    exactRevealCode D seed q' =
        exactRevealCode D seed q ↔
      (∀ j : Fin n,
        j ∈ exactFairAliceQuestionMask D seed →
          q'.1 j = q.1 j) ∧
      (∀ j : Fin n,
        j ∈ exactFairBobQuestionMask D seed →
          q'.2 j = q.2 j) := by sorry
