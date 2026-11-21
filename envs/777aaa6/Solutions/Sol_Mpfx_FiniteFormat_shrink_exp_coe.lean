-- Prove2me | solution 1 for Mpfx.FiniteFormat.shrink_exp_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:49:59.534755+00:00
-- url     : https://prove2.me/submissions/de3cd40e-c655-434a-b99a-e0648ea25cac

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution {F : FiniteFormat} (h : F.p ≠ ((1 : ℕ) : Prec)) {e : ℤ}
    (he : F.exp = (e : QExp)) : (F.shrink h).exp = ((e + 1 : ℤ) : QExp) := by
  change F.exp.map _ = _; rw [he]; rfl
end Mpfx.FiniteFormat
