-- Prove2me | solution 1 for Mpfx.WithSpecial.neg_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:21:31.966323+00:00
-- url     : https://prove2.me/submissions/e0cd1cbb-f0b2-474f-b9be-3749fd26f788

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace WithSpecial
theorem _root_.solution {α : Type} [Neg α] (a : α) :
    (WithSpecial.finite a).neg = .finite (-a) := rfl
end WithSpecial
end Mpfx
