-- Prove2me | solution 1 for Mpfx.Dyadic.precisionAtMost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:23.437024+00:00
-- url     : https://prove2.me/submissions/c7902f5e-14cd-49fd-b988-bc44adf2fe58

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {p₁ p₂ : Prec} (h : p₁ ≤ p₂) {x : Dyadic}
    (hx : precisionAtMost p₁ x) : precisionAtMost p₂ x := by
  cases p₂ using ENat.recTopCoe with
  | top => trivial
  | coe p₂ =>
    cases p₁ using ENat.recTopCoe with
    | top => exact absurd (top_le_iff.mp h) (WithTop.coe_ne_top)
    | coe p₁ =>
      obtain ⟨c, e, hc, hb⟩ := hx
      refine ⟨c, e, hc, ?_⟩
      have hp_le : p₁ ≤ p₂ := by exact_mod_cast WithTop.coe_le_coe.mp h
      exact lt_of_lt_of_le hb (pow_le_pow_right₀ (by norm_num) hp_le)
end Mpfx.Dyadic
