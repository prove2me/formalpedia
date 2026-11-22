-- Prove2me | solution 1 for Mpfx.ulp_le_half_ulp_of_canonicalExp_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:10:59.673004+00:00
-- url     : https://prove2.me/submissions/72f135b2-ab0c-45db-87ff-96dd35aaa2fc

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_ulp_of_ne_zero

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {x : ℝ}
    (hx : x ≠ 0) (h : F₂.canonicalExp x < F₁.canonicalExp x) :
    ulp F₂ x ≤ ulp F₁ x / 2 := by
  rw [ulp_of_ne_zero F₁ hx, ulp_of_ne_zero F₂ hx]
  have hle : F₂.canonicalExp x ≤ F₁.canonicalExp x - 1 := by omega
  calc (2 : ℝ) ^ F₂.canonicalExp x
      ≤ (2 : ℝ) ^ (F₁.canonicalExp x - 1) := zpow_le_zpow_right₀ (by norm_num) hle
    _ = (2 : ℝ) ^ F₁.canonicalExp x / 2 := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
end Mpfx
