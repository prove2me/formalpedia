-- Prove2me | solution 1 for P2M_List_zipWith__map_758ae55ee09f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:47.053726+00:00
-- url     : https://prove2.me/submissions/78138aa0-576c-4eee-8edd-402200b260c7

import Batteries.Data.List.Basic
import Mathlib.Logic.IsEmpty
import Definitions.Def_BruhatTits_Utils_List

set_option autoImplicit false

namespace List
theorem _root_.solution {α α' β β' γ γ' δ : Type*} (f : α' → β' → γ' → δ)
    (fa : α → α') (fb : β → β') (fc : γ → γ')
    (la : List α) (lb : List β) (lc : List γ) :
    List.zipWith₃ f (la.map fa) (lb.map fb) (lc.map fc) =
      List.zipWith₃ (fun a b c ↦ f (fa a) (fb b) (fc c)) la lb lc := by
  match la, lb, lc with
  | [], _, _ => simp [List.zipWith₃]
  | _, [], _ => simp [List.zipWith₃]
  | _, _, [] => simp [List.zipWith₃]
  | (a :: as), (b :: bs), (c :: cs) =>
    simp [List.zipWith₃]
    apply solution
end List
