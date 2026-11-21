-- Prove2me | Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
-- name    : Mpfx_DoubleRounding_Counterexample_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:45:37.22872+00:00
-- url     : https://prove2.me/theorems/e9e0dc16-0343-48ed-a2c7-28daab170b90
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean

import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
namespace Mpfx
namespace Cex
def Isolated (F : FiniteFormat) (m : Dyadic) (K : ℤ) : Prop :=
  ∀ v ∈ F.unbounded, |(v : ℝ) - m| < (2 : ℝ) ^ K → v = m
def Adjacent (F : FiniteFormat) (u u' : Dyadic) : Prop :=
  u ∈ F.unbounded ∧ u' ∈ F.unbounded ∧ (u : ℝ) < u' ∧
    ∀ v ∈ F.unbounded, (v : ℝ) < u' → (v : ℝ) ≤ u
end Cex
end Mpfx


