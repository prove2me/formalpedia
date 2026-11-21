-- Prove2me | solution 1 for Mpfx.neighbor_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:36.911469+00:00
-- url     : https://prove2.me/submissions/42c469d4-8678-434c-9152-1c1da9c0971d

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
import Theorems.Thm_Mpfx_abs_floor_add_one_le_of_abs_lt
import Theorems.Thm_Mpfx_abs_floor_le_of_abs_lt
import Theorems.Thm_Mpfx_floor_mantissa_lt


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} (x : ℝ) {m : ℤ}
    (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) {p : ℕ} (hp : F.p = p) :
    |m| ≤ 2 ^ p := by
  have hs := floor_mantissa_lt (F := F) (x := x) hp
  rcases hm with rfl | rfl
  · exact abs_floor_le_of_abs_lt (N := 2 ^ p) (by push_cast; exact hs)
  · exact abs_floor_add_one_le_of_abs_lt hs
end Mpfx
