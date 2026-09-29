-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceContext_prefix_before_marked
-- name    : QuantumParallelRepetition.exactReverseAliceContext_prefix_before_marked
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:52:11.860365+00:00
-- url     : https://prove2.me/theorems/b10e7ac1-4e69-4311-96c9-db263dff96f7
-- title:
--   Alice's reverse context recovers the seed's left prefix as the block before the marked coordinate
-- statement:
--   Let $M$ be a finite type with decidable equality and let $\sigma$ be a forward seed on $M$: a marked coordinate $i$, a two-colouring $\pi$ splitting $M\setminus\{i\}$ into a left block $L(\sigma)$ and a right block $R(\sigma)$, orderings of the two blocks, and cut positions $\ell\in\{0,\dots,|L(\sigma)|\}$ and $r\in\{0,\dots,|R(\sigma)|\}$. Write $L_{<\ell}(\sigma)=\{\,j\in L(\sigma):\operatorname{rank}_L(j)<\ell\,\}$ for the seed's left prefix. Alice's reverse description of $\sigma$ is built on the side $A(\sigma)=\{i\}\cup L(\sigma)$, enumerated by inserting $i$ into the ordering of $L(\sigma)$ at position $\ell$, with $R(\sigma)$, its ordering and $r$ playing the role of the complementary side. For a side equipped with an enumeration, the *block before* a position $p$ is the set of side elements of rank strictly less than $p$. The theorem states that taking $p$ to be the rank of the marked coordinate $i$ inside $A(\sigma)$ returns exactly the seed's left prefix:
--   $$\big\{\,j\in A(\sigma)\ :\ \operatorname{rank}_A(j)<\operatorname{rank}_A(i)\,\big\}\;=\;L_{<\ell}(\sigma).$$
--   This is the compatibility fact that lets the reverse description of a seed by a side, a context and a marker be translated back into the forward description by a coordinate, a colouring, orderings and cuts.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L30788-L30846

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_18
import Theorems.Thm_QuantumParallelRepetition_exactReverseLeftSide_coordinate_mem
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
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
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseAliceContext_prefix_before_marked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextPrefixBefore
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
      exactLeftPrefix seed := by sorry
