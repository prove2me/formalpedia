-- Prove2me | Definitions.Def_Fpy_Value
-- name    : Fpy_Value
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:30:41.283269+00:00
-- url     : https://prove2.me/theorems/08b665a0-9b01-483d-98ce-9cdbf9c584bc
-- title:
--   Value
-- statement:
--   Definitions and structural lemmas for Value, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Value.lean

import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
namespace Fpy
open Mpfx
abbrev Num := WithSpecial ℝ
abbrev Label := String
inductive Val where
  | bool (b : Bool)
  | num (n : Num)
  | list (vs : List Val)
  | record (fs : List (Label × Val))
  | real
  | ctx (fs : List (Label × Val))
def Val.IsCtx : Val → Prop
  | .real | .ctx _ => True
  | _ => False
end Fpy


