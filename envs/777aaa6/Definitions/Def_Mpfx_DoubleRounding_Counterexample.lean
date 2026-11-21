-- Prove2me | Definitions.Def_Mpfx_DoubleRounding_Counterexample
-- name    : Mpfx_DoubleRounding_Counterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:46:22.806737+00:00
-- url     : https://prove2.me/theorems/9715d662-6843-406b-ba3c-5b77e02a0963
-- title:
--   Counterexample
-- statement:
--   Definitions and structural lemmas for Counterexample, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
set_option autoImplicit true
namespace Mpfx
namespace Cex
def Disagrees (F₂ : FiniteFormat) (rm₂ : RoundingMode) (F₁ : FiniteFormat)
    (rm₁ : RoundingMode) : Prop :=
  ∃ (x : ℝ) (z w y : Dyadic), RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ (z : ℝ) w ∧
    RoundsInBound F₁ rm₁ x y ∧ w ≠ y
section Anchors
variable {F₁ : ParityFormat}
end Anchors
end Cex
end Mpfx


