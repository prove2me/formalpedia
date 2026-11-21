-- Prove2me | solution 1 for Mpfx.precisionAtMost_one_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:26:42.677058+00:00
-- url     : https://prove2.me/submissions/41e41d79-4982-43ae-a690-2b4a5c82fff4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe
import Theorems.Thm_Mpfx_abs_one_lt_two_pow

attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {p : Prec} (hp : p ≠ 0) (k : ℤ) :
    Dyadic.precisionAtMost p (Dyadic.ofIntZpow 1 k) := by
  cases p using ENat.recTopCoe with
  | top => trivial
  | coe p =>
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, k, by rw [Dyadic.coe_rat_ofIntZpow], ?_⟩
    exact abs_one_lt_two_pow (Nat.pos_of_ne_zero (by intro hz; apply hp; rw [hz]; rfl))
end Mpfx
