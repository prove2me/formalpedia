-- Prove2me | solution 1 for Mpfx.FiniteFormat.shrink_exp_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:02.233697+00:00
-- url     : https://prove2.me/submissions/14d303e7-2fa1-4873-ac0f-7f9e0b9b7779

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution {F : FiniteFormat} (h : F.p ≠ ((1 : ℕ) : Prec))
    (he : F.exp = ⊥) : (F.shrink h).exp = ⊥ := by
  change F.exp.map _ = _; rw [he]; rfl
end Mpfx.FiniteFormat
