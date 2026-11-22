-- Prove2me | solution 1 for Mpfx.FiniteFormat.le_maxFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:28.725095+00:00
-- url     : https://prove2.me/submissions/662bab49-08c9-406a-bd56-1f0bce044375

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Special
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem


set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (hb : F.b ≠ ⊤) {v : Dyadic} (hv : v ∈ F) :
    (v : ℝ) ≤ (F.maxFinite hb : ℝ) := by
  obtain ⟨-, -, hmax⟩ := F.maxFinite_spec hb
  refine hmax v (mem_unbounded_of_mem hv) ?_
  have h := hv.2.2
  rw [← WithTop.coe_untop F.b hb] at h
  exact (le_abs_self _).trans (abs_coe_real_le_of_boundOK h)
end Mpfx.FiniteFormat
