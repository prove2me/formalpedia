-- Prove2me | solution 1 for Mpfx.NonNegDyadic.le_iff_coe_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:21.000194+00:00
-- url     : https://prove2.me/submissions/27107b9a-b095-4daa-9f93-d3c4e8bd3148

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace NonNegDyadic
theorem _root_.solution {a b : NonNegDyadic} :
    a ≤ b ↔ ((a.val : Dyadic) : ℝ) ≤ ((b.val : Dyadic) : ℝ) := by
  rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, Rat.cast_le]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
end NonNegDyadic
end Mpfx
