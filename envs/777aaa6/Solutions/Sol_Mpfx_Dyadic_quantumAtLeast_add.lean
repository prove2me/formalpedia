-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:29:15.420836+00:00
-- url     : https://prove2.me/submissions/7c6dd033-c43a-49f1-94c5-be7d97538045

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a + b) := by
  cases e using QExp.recBotCoe with
  | bot => trivial
  | coe e =>
    obtain ⟨ca, hca⟩ := (Dyadic.quantumAtLeast_coe_real e a).mp ha
    obtain ⟨cb, hcb⟩ := (Dyadic.quantumAtLeast_coe_real e b).mp hb
    refine (Dyadic.quantumAtLeast_coe_real e (a + b)).mpr ⟨ca + cb, ?_⟩
    rw [show ((a + b : Dyadic) : ℝ) = (a : ℝ) + (b : ℝ) from by push_cast; ring, hca, hcb]
    push_cast; ring
end Mpfx.Dyadic
