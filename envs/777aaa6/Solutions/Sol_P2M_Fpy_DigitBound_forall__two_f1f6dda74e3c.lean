-- Prove2me | solution 1 for P2M_Fpy_DigitBound_forall__two_f1f6dda74e3c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:18:23.516347+00:00
-- url     : https://prove2.me/submissions/56401462-8456-4dac-980d-3ac844b13c08

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {α β : Type} {R : α → β → Prop} {a₁ a₂ : α} {l : List β}
    (h : List.Forall₂ R [a₁, a₂] l) : ∃ b₁ b₂, l = [b₁, b₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by
  rcases h with _ | ⟨h₁, _ | ⟨h₂, h'⟩⟩; cases h'; exact ⟨_, _, rfl, h₁, h₂⟩
end Fpy.DigitBound
