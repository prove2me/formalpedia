-- Prove2me | solution 1 for Mpfx.boundOK_of_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:30:28.536068+00:00
-- url     : https://prove2.me/submissions/7daa43a4-da52-4625-afc9-6271ed21fbe5

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {b : Bound} {lo hi g : Dyadic}
    (hblo : Format.boundOK b lo) (hbhi : Format.boundOK b hi)
    (h1 : (lo : ℝ) ≤ (g : ℝ)) (h2 : (g : ℝ) ≤ (hi : ℝ)) :
    Format.boundOK b g := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    have h1' : (lo : ℚ) ≤ (g : ℚ) := by
      exact_mod_cast h1
    have h2' : (g : ℚ) ≤ (hi : ℚ) := by
      exact_mod_cast h2
    change |(g : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hblo).1], by linarith [(abs_le.mp hbhi).2]⟩
end Mpfx
