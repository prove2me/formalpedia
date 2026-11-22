-- Prove2me | solution 1 for Fpy.precisionAtMost_pHat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:42.315755+00:00
-- url     : https://prove2.me/submissions/e8c372c4-64ef-4328-b4e8-f9da21773859

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Mpfx_Format_precisionAtMost_bitsFor


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F : Format} {d : Mpfx.Dyadic} (hd : d ∈ F) :
    Dyadic.precisionAtMost F.pHat d := by
  have hbits : Dyadic.precisionAtMost F.bits d := by
    unfold Format.bits
    obtain ⟨_, hq, hb⟩ := hd
    split
    · next b e hb' he' =>
      rw [he'] at hq
      rw [hb'] at hb
      refine Format.precisionAtMost_bitsFor hq ?_
      change |(d : ℚ)| ≤ ((b.1 : Mpfx.Dyadic) : ℚ) at hb
      exact_mod_cast hb
    · trivial
  unfold Format.pHat
  rcases min_choice F.p F.bits with h | h <;> rw [h]
  · exact hd.1
  · exact hbits
end Fpy
