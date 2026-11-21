-- Prove2me | solution 1 for Mpfx.Format.neg_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:00:06.224701+00:00
-- url     : https://prove2.me/submissions/2c775193-0f6b-4451-a907-e11f83d1c58e

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
import Theorems.Thm_Mpfx_FiniteFormat_mem_neg_iff
import Theorems.Thm_Mpfx_Format_mem_neg_iff


set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution (F : Format) : -F.values ⊆ (opNeg F).values := by
  rintro (d | s) h
  · exact (mem_neg_iff F d).mp h
  · exact h
end Mpfx.Format
