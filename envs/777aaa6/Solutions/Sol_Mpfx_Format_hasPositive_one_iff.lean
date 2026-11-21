-- Prove2me | solution 1 for Mpfx.Format.hasPositive_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:56.663675+00:00
-- url     : https://prove2.me/submissions/31d5de4e-bde4-4e26-a2eb-ce6281baa770

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Format_neg_mem
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_zero



set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} : F.HasPositive 1 ↔ F.Nontrivial := by
  refine ⟨fun ⟨f, _, hf⟩ => ⟨f 0, (hf 0).1, fun h => ?_⟩, fun ⟨d, hd, hne⟩ => ?_⟩
  · have := (hf 0).2
    rw [h, Dyadic.coe_real_zero] at this
    exact lt_irrefl _ this
  · have hne' : (d : ℝ) ≠ 0 := fun h => hne (Dyadic.ext_real (by rw [h, Dyadic.coe_real_zero]))
    rcases hne'.lt_or_gt with hneg | hpos
    · exact ⟨fun _ => -d, Subsingleton.strictMono _,
        fun _ => ⟨neg_mem hd, by rw [Dyadic.coe_real_neg]; linarith⟩⟩
    · exact ⟨fun _ => d, Subsingleton.strictMono _, fun _ => ⟨hd, hpos⟩⟩
end Mpfx.Format
