-- Prove2me | Definitions.Def_Mpfx_Format_Parity
-- name    : Mpfx_Format_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:39:51.802177+00:00
-- url     : https://prove2.me/theorems/3c2514b3-f253-4510-954b-7ec16f60a203
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
set_option autoImplicit true
namespace Mpfx
structure ParityFormat extends FiniteFormat where
  parity : toFormat.p ≠ 1 ∨ toFormat.exp ≠ ⊥
namespace FiniteFormat
def IsOdd (F : FiniteFormat) (y : Dyadic) : Prop :=
  ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (F.numDigits (y : ℝ)).toNat c e y ∧
    (if F.p = ((1 : ℕ) : Prec) then
        Odd (e - WithBot.unbotD 0 F.exp + 1)
      else
        Odd c)
def IsEven (F : FiniteFormat) (y : Dyadic) : Prop :=
  y ∈ F.unbounded ∧ ¬ F.IsOdd y
end FiniteFormat
end Mpfx


