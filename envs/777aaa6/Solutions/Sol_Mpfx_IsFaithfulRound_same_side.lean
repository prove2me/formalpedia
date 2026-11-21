-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.same_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:37.229729+00:00
-- url     : https://prove2.me/submissions/30b33c90-da2c-48db-bb8f-e20fc381d6a2

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {z m : Dyadic}
    (h : IsFaithfulRound F x z) (hm : m ∈ F) (hxm : x ≠ (m : ℝ)) (hzm : (z : ℝ) ≠ m) :
    0 < (x - m) * ((z : ℝ) - m) := by
  rcases h with ⟨-, hzx, hmax⟩ | ⟨-, hxz, hmin⟩ <;> rcases lt_or_gt_of_ne hxm with h | h
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · exact mul_pos (by linarith) (by linarith [lt_of_le_of_ne (hmax m hm h.le) hzm.symm])
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith [lt_of_le_of_ne (hmin m hm h.le) hzm])
  · exact mul_pos (by linarith) (by linarith)
end IsFaithfulRound
end Mpfx
