-- Prove2me | Theorems.Thm_P2M_List_zipWith__map_758ae55ee09f
-- name    : P2M_List_zipWith__map_758ae55ee09f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:48:02.077678+00:00
-- url     : https://prove2.me/theorems/763ead56-d13d-4ad3-b295-c5a9a4c4badb
-- title:
--   P2 M List zip With  map 758ae55ee09f: P2 M List zip With  map 758ae55ee09f
-- statement:
--   The P2 M List zip With  map 758ae55ee09f construction uses the P2 M List zip With  map 758ae55ee09f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/List.lean#L4-L15
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/List.lean#L4-L15

import Batteries.Data.List.Basic
import Mathlib.Logic.IsEmpty
import Definitions.Def_BruhatTits_Utils_List
set_option autoImplicit false

theorem P2M_List_zipWith__map_758ae55ee09f {α α' β β' γ γ' δ : Type*} (f : α' → β' → γ' → δ)
    (fa : α → α') (fb : β → β') (fc : γ → γ')
    (la : List α) (lb : List β) (lc : List γ) :
    List.zipWith₃ f (la.map fa) (lb.map fb) (lc.map fc) =
      List.zipWith₃ (fun a b c ↦ f (fa a) (fb b) (fc c)) la lb lc := by sorry

alias «List».«zipWith₃_map» := P2M_List_zipWith__map_758ae55ee09f
