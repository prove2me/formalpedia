-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceMarkerDecode_rightInverse
-- name    : QuantumParallelRepetition.exactReverseAliceMarkerDecode_rightInverse
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:03:31.225809+00:00
-- url     : https://prove2.me/theorems/68825b21-cc4e-4bcc-a390-63d0e58dcd1e
-- title:
--   Decoding a side, context and marker recovers a seed with exactly that code (Alice)
-- statement:
--   Fix a finite type $M$, a subset $s\subseteq M$, a side context $c$ over $s$ (recording the complementary set, an enumeration of $s$, an enumeration of the complement, a cut in the complement and one extra bit) and a marker position $m\in\{0,\dots,|s|-1\}$. The decoding procedure builds a seed whose marked coordinate is the $m$-th element of $s$ under $c$'s enumeration, whose colouring is the canonical Alice colouring for $(s,i,c\text{'s bit})$, and whose orders and cuts are read off from $c$ and $m$. The theorem asserts that encoding this seed returns the original data exactly: the Alice side, context and marker of the decoded seed are $s$, $c$ and $m$. Together with injectivity of the encoding, this makes the encoding a bijection between seeds and such triples.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L33679-L33760

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
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
import Mathlib.Data.Finset.SDiff
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
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseAliceMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseAliceMarkerCode
        (exactReverseAliceMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by sorry
