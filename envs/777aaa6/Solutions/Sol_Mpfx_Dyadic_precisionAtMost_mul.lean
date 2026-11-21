-- Prove2me | solution 1 for Mpfx.Dyadic.precisionAtMost_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:28:02.490586+00:00
-- url     : https://prove2.me/submissions/ca349171-ca06-476e-9d6b-aa90730f23fb

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {p₁ p₂ : Prec} {x y : Dyadic}
    (hx : precisionAtMost p₁ x) (hy : precisionAtMost p₂ y) :
    precisionAtMost (p₁ + p₂) (x * y) := by
  cases p₁ using ENat.recTopCoe with
  | top => rw [top_add]; trivial
  | coe a =>
    cases p₂ using ENat.recTopCoe with
    | top => rw [add_top]; trivial
    | coe b =>
      rw [precisionAtMost_coe] at hx hy
      obtain ⟨c1, e1, hxeq, hc1⟩ := hx
      obtain ⟨c2, e2, hyeq, hc2⟩ := hy
      rw [← Nat.cast_add, precisionAtMost_coe]
      refine ⟨c1 * c2, e1 + e2, ?_, ?_⟩
      · change ((x * y : Dyadic) : ℚ) = _
        push_cast
        rw [hxeq, hyeq, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        ring
      · rw [pow_add, abs_mul]
        exact mul_lt_mul'' hc1 hc2 (abs_nonneg _) (abs_nonneg _)
end Mpfx.Dyadic
