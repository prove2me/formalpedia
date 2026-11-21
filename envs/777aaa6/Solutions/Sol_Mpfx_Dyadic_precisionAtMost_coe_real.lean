-- Prove2me | solution 1 for Mpfx.Dyadic.precisionAtMost_coe_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:26:37.064706+00:00
-- url     : https://prove2.me/submissions/e129bd07-3f73-42ea-977d-6aae9ceb229c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (p : ℕ) (x : Dyadic) :
    precisionAtMost (p : Prec) x ↔
      ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ p := by
  rw [precisionAtMost_coe]
  refine ⟨fun ⟨c, e, hc, hb⟩ => ⟨c, e, ?_, hb⟩, fun ⟨c, e, hc, hb⟩ => ⟨c, e, ?_, hb⟩⟩
  · rw [coe_real_eq_ratCast, hc]; push_cast; ring
  · have h : ((x : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ) := by
      rw [← coe_real_eq_ratCast, hc]; push_cast; ring
    exact_mod_cast h
end Mpfx.Dyadic
