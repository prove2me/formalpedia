-- Prove2me | solution 1 for Mpfx.Format.Nontrivial.p_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:30:24.128825+00:00
-- url     : https://prove2.me/submissions/b45800b9-ca80-487f-8d48-5fdac866fdeb

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_zero_iff_eq_zero


set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
namespace Nontrivial
theorem _root_.solution {F : Format} (h : F.Nontrivial) : F.p ≠ 0 := by
  obtain ⟨d, hd, hd_ne⟩ := h
  intro h0
  have hp := hd.1
  rw [h0] at hp
  exact hd_ne (Dyadic.precisionAtMost_zero_iff_eq_zero.mp hp)
end Nontrivial
end Mpfx.Format
