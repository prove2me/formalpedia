-- Prove2me | Definitions.Def_Mpfx_Rounding_Op_Defs
-- name    : Mpfx_Rounding_Op_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:41:42.328847+00:00
-- url     : https://prove2.me/theorems/e0a52b88-a793-4472-a4e0-763660685bcb
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Defs.lean

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
set_option autoImplicit true
namespace Mpfx
attribute [local instance] Classical.propDecidable
noncomputable def rndInt (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (e : ℤ) : ℤ :=
  let s := x * (2 : ℝ) ^ (-e)
  let lo := ⌊s⌋
  let δ := s - (lo : ℝ)
  match rm with
  | .toZero    => if 0 ≤ x then ⌊s⌋ else ⌈s⌉
  | .toNegative => ⌊s⌋
  | .toPositive => ⌈s⌉
  | .awayZero   => if 0 ≤ x then ⌈s⌉ else ⌊s⌋
  | .toOdd =>
      if (lo : ℝ) = s then lo                   -- x is exactly on lo
      else if F.IsOdd (Dyadic.ofIntZpow lo e) then lo else lo + 1
  | .nearest .awayZero =>
      if δ < 1/2 then lo
      else if 1/2 < δ then lo + 1
      else if 0 ≤ x then lo + 1 else lo         -- tie: away from zero
  | .nearest .toEven =>
      if δ < 1/2 then lo
      else if 1/2 < δ then lo + 1
      else if F.IsEven (Dyadic.ofIntZpow lo e) then lo else lo + 1
noncomputable def rndUnbounded (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (_h_undef : ¬ F.IsUndefined rm) : Dyadic :=
  Dyadic.ofIntZpow (rndInt F rm x (F.canonicalExp x)) (F.canonicalExp x)
noncomputable def rnd (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (rm : RoundingMode) : WithSpecial ℝ → RoundResult
  | .special s => .value (S.map s)
  | .finite x =>
    if h_undef : F.IsUndefined rm then
      .undefined
    else
      let y := rndUnbounded F rm x h_undef
      if Format.boundOK F.b y then .value (.finite y)
      else .value (O.map (decide ((y : ℚ) < 0)))
end Mpfx


