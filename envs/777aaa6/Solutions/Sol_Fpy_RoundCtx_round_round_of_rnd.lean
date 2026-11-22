-- Prove2me | solution 1 for Fpy.RoundCtx.round_round_of_rnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:33:01.46534+00:00
-- url     : https://prove2.me/submissions/97ff3b0c-b6e0-412a-aa15-dc4670a0eb7a

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_RoundCtx_exists_rnd_eq


set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}
namespace Fpy
namespace RoundCtx
theorem _root_.solution {c₁ c₂ : RoundCtx} {n : Num}
    (h : ∀ u, rnd c₂.F c₂.S c₂.O c₂.rm n = .value u →
      rnd c₁.F c₁.S c₁.O c₁.rm u.toReal = rnd c₁.F c₁.S c₁.O c₁.rm n) :
    c₁.round (c₂.round n) = c₁.round n := by
  obtain ⟨u, hu, hn⟩ := c₂.exists_rnd_eq n
  obtain ⟨w, hw, hw'⟩ := c₁.exists_rnd_eq n
  obtain ⟨w', hw'', he⟩ := c₁.exists_rnd_eq u.toReal
  rw [h u hu, hw] at hw''
  rw [hn, he, hw', RoundResult.value.inj hw'']
end RoundCtx
end Fpy
