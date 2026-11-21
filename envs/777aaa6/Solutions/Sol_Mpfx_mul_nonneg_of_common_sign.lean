-- Prove2me | solution 1 for Mpfx.mul_nonneg_of_common_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:58.34949+00:00
-- url     : https://prove2.me/submissions/7aed8e99-7e6b-4d59-95ee-e3b20c153035

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {x : ℝ} {y z : ℝ}
    (hyx : y * x ≥ 0) (hzx : z * x ≥ 0) (hy0 : x = 0 → y = 0) :
    y * z ≥ 0 := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [hy0 hx, zero_mul]
  · have hx2 : 0 < x ^ 2 := by positivity
    nlinarith [mul_nonneg hyx hzx]
end Mpfx
