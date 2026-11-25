-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture96_conjecture96
-- name    : WrittenOnTheWallII.GraphConjecture96.conjecture96
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:03.975856+00:00
-- url     : https://prove2.me/theorems/1a8ff18c-d911-5c43-bfbe-479d254cb962
-- title:
--   Graph Conjecture96: conjecture96
-- statement:
--   The Graph Conjecture96 construction uses the conjecture96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Upstream.lean#L59-L63
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Upstream.lean#L59-L63

module
public import Definitions.Def_OpenMath_WOWII96
public import Definitions.Def_OpenMath_WOWII19
public import Definitions.Def_OpenMath_Upstream
public import Theorems.Thm_OpenMath_WOWII96_conjecture96

set_option autoImplicit true
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture96
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem WrittenOnTheWallII.GraphConjecture96.conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by sorry
