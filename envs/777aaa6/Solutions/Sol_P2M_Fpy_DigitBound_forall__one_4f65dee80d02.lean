-- Prove2me | solution 1 for P2M_Fpy_DigitBound_forall__one_4f65dee80d02
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:18:19.51846+00:00
-- url     : https://prove2.me/submissions/d3fb5e32-dbd0-4fc5-a913-e67d07b6a3b3

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {α β : Type} {R : α → β → Prop} {a : α} {l : List β}
    (h : List.Forall₂ R [a] l) : ∃ b, l = [b] ∧ R a b := by
  rcases h with _ | ⟨h, h'⟩; cases h'; exact ⟨_, rfl, h⟩
end Fpy.DigitBound
