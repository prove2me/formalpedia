-- Prove2me | Theorems.Thm_QuantumParallelRepetition_aliceMartingaleEntropyBudget
-- name    : QuantumParallelRepetition.aliceMartingaleEntropyBudget
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T02:58:23.927674+00:00
-- url     : https://prove2.me/theorems/c521fb08-6ff3-461b-a7bb-d9ccad133960
-- title:
--   Alice's averaged entropy increment is at most the postselected martingale rate
-- statement:
--   Fix a game $G$, a repetition count $n$, a strategy $S$ for $G^{\otimes n}$, and a conditioned set $D\subseteq\{1,\dots,n\}$ whose complement is nonempty and whose postselection mass $p_D$, the probability that the verifier accepts in every coordinate of $D$, is positive. Draw an ordering $\pi$ of the remaining coordinates $\{1,\dots,n\}\setminus D$ uniformly at random together with a uniformly random position $k$, and let $\Delta^{A}(\pi,k)$ denote Alice's total entropy increment at the coordinate sitting in position $k$, when the coordinates before position $k$ have already been revealed. Then
--
--   $$\mathbb{E}_{\pi,k}\big[\Delta^{A}(\pi,k)\big]\;\le\;p_D\cdot\frac{\log(1/p_D)+|D|\log\big(|A|\,|B|\big)}{\big|\{1,\dots,n\}\setminus D\big|}.$$
--
--   The right-hand factor is the martingale rate: the total logarithmic budget of the postselected experiment spread evenly over the coordinates not yet conditioned on.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L24988-L25007

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.aliceMartingaleEntropyBudget
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < repeatedPostselectionMass G n S D) :
    sourceUniformPermutationAverage D
        (sourcePermutationAliceEntropyIncrement G n S D) ≤
      repeatedPostselectionMass G n S D *
        martingaleRate G n S D := by sorry
