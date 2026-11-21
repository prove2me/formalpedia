-- Prove2me | solution 1 for Mpfx.Format.neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:30:50.403842+00:00
-- url     : https://prove2.me/submissions/1e0aff15-5091-49c4-b99d-c8937b7efc8d

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Format_boundOK_neg
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg


set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} {d : Dyadic} (h : d ∈ F) : (-d) ∈ F := by
  obtain ⟨hp, he, hb⟩ := h
  exact ⟨Dyadic.precisionAtMost_neg hp, Dyadic.quantumAtLeast_neg he, boundOK_neg hb⟩
end Mpfx.Format
