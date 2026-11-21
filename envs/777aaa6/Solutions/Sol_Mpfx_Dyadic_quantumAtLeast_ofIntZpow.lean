-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_ofIntZpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:26:47.215248+00:00
-- url     : https://prove2.me/submissions/f5b193eb-4417-436e-aaa1-2d18294599b4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {e : QExp} {c k : ℤ} (he : e ≤ (k : QExp)) :
    quantumAtLeast e (ofIntZpow c k) :=
  quantumAtLeast_anti he ⟨c, by rw [coe_rat_ofIntZpow]⟩
end Mpfx.Dyadic
