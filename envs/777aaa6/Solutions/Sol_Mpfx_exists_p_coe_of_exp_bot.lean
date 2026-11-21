-- Prove2me | solution 1 for Mpfx.exists_p_coe_of_exp_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:59.763683+00:00
-- url     : https://prove2.me/submissions/74263082-7094-4a4d-9a73-9a5d820daa93

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} (he : F.exp = ⊥) :
    ∃ p : ℕ, F.p = (p : Prec) := by
  cases hc : F.p using ENat.recTopCoe with
  | top => exact absurd F.finite (by push Not; exact ⟨hc, he⟩)
  | coe p => exact ⟨p, rfl⟩
end Mpfx
