-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceUniformMarkedSeed_sum
-- name    : QuantumParallelRepetition.exactReverseAliceUniformMarkedSeed_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:26:47.622361+00:00
-- url     : https://prove2.me/theorems/16cbec5f-11bc-496b-babe-8e63cea9aee8
-- title:
--   Under the seed law the marked position is uniform in Alice's side
-- statement:
--   Recall that a *seed* over a finite type $M$ is a tuple $\sigma=(i,\pi,\tau_L,\tau_R,\ell,r)$ consisting of a marked coordinate $i\in M$, a two-colouring $\pi:M\to\{0,1\}$, orderings $\tau_L,\tau_R$ of the two colour classes $L(\sigma)=\{j\neq i:\pi(j)=0\}$ and $R(\sigma)=\{j\neq i:\pi(j)=1\}$, and cut positions $\ell\in\{0,\dots,|L(\sigma)|\}$, $r\in\{0,\dots,|R(\sigma)|\}$; the seed weight $w(\sigma)$ is the uniform product weight on these ingredients. Write $A(\sigma)=\{i\}\cup L(\sigma)$, let $\mathrm{ctx}_A(\sigma)$ be the associated side context and let $m(\sigma)$ be the position of the marked coordinate in the enumeration of $A(\sigma)$. Assume $M$ is nonempty, and let $F(s,c,m)$ be an arbitrary real statistic of a side, a context over that side and a position. The theorem states that averaging $F$ uniformly over positions gives the same seed-weighted total as evaluating it at the actual marked position: $$\sum_{\sigma}w(\sigma)\,\frac{1}{|A(\sigma)|}\sum_{m=0}^{|A(\sigma)|-1}F\big(A(\sigma),\mathrm{ctx}_A(\sigma),m\big)\;=\;\sum_{\sigma}w(\sigma)\,F\big(A(\sigma),\mathrm{ctx}_A(\sigma),m(\sigma)\big).$$ In probabilistic terms, conditionally on Alice's side and its context, the marked position is uniformly distributed.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L34110-L34216

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Theorems.Thm_QuantumParallelRepetition_exactReverseLeftSide_coordinate_mem
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
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseAliceUniformMarkedSeed_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (statistic : (side : Finset M) →
      ExactReverseSideContext M side → Fin side.card → ℝ) :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseLeftSide seed).card,
          statistic (exactReverseLeftSide seed)
            (exactReverseAliceContext seed) marker) /
          ((exactReverseLeftSide seed).card : ℝ))) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          statistic (exactReverseLeftSide seed)
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩) := by sorry
