-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactInsertedPrefixBefore_marker_eq
-- name    : QuantumParallelRepetition.exactInsertedPrefixBefore_marker_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:40:37.982418+00:00
-- url     : https://prove2.me/theorems/9ec49441-b0f3-4f84-81d9-f5a7b81cc906
-- title:
--   Inserting the marked element at the cut leaves the block before the cut unchanged
-- statement:
--   Let $M$ be a finite type with decidable equality, let $s\subseteq M$ be a subset, let $i\in M$ with $i\notin s$, let $\rho:s\xrightarrow{\ \sim\ }\{0,1,\dots,|s|-1\}$ be an enumeration of $s$, and fix a cut position $c\in\{0,1,\dots,|s|\}$. Insert $i$ into the enumeration at position $c$: this produces the enumeration $\rho^{+}$ of $s\cup\{i\}$ characterised by
--   $$\rho^{+}(i)=c,\qquad \rho^{+}(j)=\begin{cases}\rho(j), & \rho(j)<c,\\ \rho(j)+1, & \rho(j)\ge c,\end{cases}\quad (j\in s),$$
--   that is, elements of $s$ keep their rank when it lies below $c$ and are shifted up by one when it is at least $c$. The theorem states that the elements of $s\cup\{i\}$ whose inserted rank is strictly below $c$ are exactly the elements of $s$ whose original rank is strictly below $c$:
--   $$\big\{\,j\in s\cup\{i\}\ :\ \rho^{+}(j)<c\,\big\}\;=\;\big\{\,j\in s\ :\ \rho(j)<c\,\big\}.$$
--   In particular the inserted marker never belongs to this block, since its rank is exactly $c$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L30407-L30458

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_18
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sets
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
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactInsertedPrefixBefore_marker_eq
    {M : Type*} [Fintype M] [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    exactInsertedPrefixBefore i side not_mem rank cut =
      (Finset.univ.filter
        (fun j : {j : M // j ∈ side} =>
          (rank j).val < cut.val)).image Subtype.val := by sorry
