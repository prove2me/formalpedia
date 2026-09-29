-- Prove2me | Theorems.Thm_B3FreeContrarian_rankSupport_weakCubeFree
-- name    : B3FreeContrarian.rankSupport_weakCubeFree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:59:45.399587+00:00
-- url     : https://prove2.me/theorems/cfb17199-5178-460d-a289-69cd1e04b951
-- title:
--   RankSupport weakCubeFree
-- statement:
--   Formal statement of `B3FreeContrarian.rankSupport_weakCubeFree` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem B3FreeContrarian.rankSupport_weakCubeFree{α : Type*} [DecidableEq α]
--       {d : ℕ} (F : Finset (Finset α)) (R : Finset ℕ)
--       (hR : R.card ≤ d) (hsupport : ∀ A ∈ F, A.card ∈ R) :
--       WeakCubeFree d F := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/B3FreeContrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/B3FreeContrarian.lean#L74

-- Thm stub generated from Probability/B3FreeContrarian.lean
import Mathlib
import Definitions.Def_Probability_B3FreeContrarian

/-!
# Contrarian tests around weak and strong Boolean-cube avoidance

This file formalizes two general obstructions to a weak copy of the Boolean lattice
`B_d`, and an explicit strong-copy construction.  The rank-support theorem strengthens
the usual consecutive-layer argument: the occupied ranks need not be consecutive.
The small-family theorem gives a different obstruction and disproves the tempting
claim that merely meeting `d+1` ranks forces a copy of `B_d`.
-/

open Finset
open scoped Classical

open B3FreeContrarian





/-
Every strong copy is weak.
-/



/-
Along the canonical chain, a weak embedding has strictly increasing ranks.
-/

/-
**Arbitrary-rank obstruction.** If a family occupies at most `d` cardinality
ranks (not necessarily consecutive), then it has no weak `B_d`.
-/

theorem B3FreeContrarian.rankSupport_weakCubeFree{α : Type*} [DecidableEq α]
    {d : ℕ} (F : Finset (Finset α)) (R : Finset ℕ)
    (hR : R.card ≤ d) (hsupport : ∀ A ∈ F, A.card ∈ R) :
    WeakCubeFree d F := by sorry
