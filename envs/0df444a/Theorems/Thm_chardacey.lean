-- Prove2me | Theorems.Thm_chardacey
-- name    : chardacey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:15.846044+00:00
-- url     : https://prove2.me/theorems/e849b410-17d4-421b-bbc1-e8bceb4b97c0
-- title:
--   chardacey: chardacey
-- statement:
--   Characterization of Dacey subsets (Jenča 2023).
--       For an orthoclosed set X the following are equivalent:
--       (a) X is a Dacey subset: (B⊥)⊥ = X for every basis B of X
--       (b) B⊥ = X⊥ for every basis B of X
--       (c) B⊥ ⊆ X⊥ for every basis B of X
--       We state this as (a) ↔ (c), the non-trivial direction being (c) → (a).
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L137-L151
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L137-L151

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]

theorem chardacey {X : Set O} (hX : IsOrthoclosed X) :
    IsDaceySubset X ↔
    ∀ B : Set O, IsOrthoBase B X → orthComp B ⊆ orthComp X := by sorry
