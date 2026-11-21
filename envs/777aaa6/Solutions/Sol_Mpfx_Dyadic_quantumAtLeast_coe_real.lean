-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_coe_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:28:28.563564+00:00
-- url     : https://prove2.me/submissions/795a12df-fe94-4844-85b8-c41ff86e2c13

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : QExp) x ↔
      ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  rw [quantumAtLeast_coe]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [coe_real_eq_ratCast, hc]; push_cast; ring
  · have h : ((x : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ) := by
      rw [← coe_real_eq_ratCast, hc]; push_cast; ring
    exact_mod_cast h
end Mpfx.Dyadic
