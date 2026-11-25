-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture19_conjecture19
-- name    : WrittenOnTheWallII.GraphConjecture19.conjecture19
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:19.905198+00:00
-- url     : https://prove2.me/theorems/cedb9fda-d76c-4808-ab8a-51953c435d65
-- title:
--   Graph Conjecture19: conjecture19
-- statement:
--   The Graph Conjecture19 construction uses the conjecture19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Upstream.lean#L74-L77
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Upstream.lean#L74-L77

module
public import Definitions.Def_OpenMath_WOWII96
public import Definitions.Def_OpenMath_WOWII19
public import Definitions.Def_OpenMath_Upstream
public import Theorems.Thm_OpenMath_WOWII19_conjecture19

set_option autoImplicit true
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture19
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem WrittenOnTheWallII.GraphConjecture19.conjecture19 (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by sorry
