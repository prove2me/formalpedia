-- Prove2me | Theorems.Thm_QuantumParallelRepetition_reweightedSeed_flagged_projection_relativeEntropy_le
-- name    : QuantumParallelRepetition.reweightedSeed_flagged_projection_relativeEntropy_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T03:31:56.405459+00:00
-- url     : https://prove2.me/theorems/ee2cffca-8627-4c49-baec-13558ed24f89
-- title:
--   Relative entropy of a flagged projection of the postselected law is at most the postselection cost plus $\log|Z|$
-- statement:
--   Let $G$ be a game, $S$ a strategy for the $n$-fold repetition $G^{n}$, and $D\subseteq\{1,\dots,n\}$ a set of coordinates. Let $\lambda$ be an auxiliary probability law on a finite set $K$, let $P=\lambda\otimes\mathbb{P}_S$ be the product of $\lambda$ with the outcome law of $S$, let $W_D$ be the event that the verifier accepts in every coordinate of $D$, assume $\varepsilon:=\mathbb{P}_S[W_D]>0$, and let $Q=P(\,\cdot\mid K\times W_D)$ be the postselected law. Given any maps $f:K\times\Omega\to U$ and $g:K\times\Omega\to Z$ with $Z$ nonempty, the theorem bounds the relative entropy of the joint pushforward $(f,g)_{*}Q$ against the product reference $(f_{*}P)\otimes\mathrm{Unif}(Z)$: $$D\big((f,g)_{*}Q\;\big\|\;(f_{*}P)\otimes\mathrm{Unif}(Z)\big)\;\le\;\log\frac{1}{\varepsilon}+\log|Z| .$$ Here $D(p\|q)=\sum_i q_i\,\mathrm{kl}(p_i/q_i)$ with $\mathrm{kl}(t)=t\log t-t+1$, which is the usual Kullback-Leibler divergence for probability vectors. In words: appending an arbitrary flag taking $|Z|$ values costs at most $\log|Z|$ nats on top of the $\log(1/\varepsilon)$ paid for the postselection.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31956-L32042

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.reweightedSeed_flagged_projection_relativeEntropy_le
    {K U Z : Type*} [Fintype K] [Fintype U] [Fintype Z]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (flag_positive : 0 < Fintype.card Z)
    (projection : K × ExactOutcome X Y A B n → U)
    (flag : K × ExactOutcome X Y A B n → Z) :
    finiteRelativeEntropy
        (reweightedSeedFlaggedProjectionLaw
          seedLaw G n S D projection flag)
        (uniformFlagReference (Z := Z)
          (groupedMass projection
            (reweightedSeedPriorEventLaw seedLaw G n S).weight)) ≤
      postselectionLogCost G n S D +
        Real.log (Fintype.card Z : ℝ) := by sorry
