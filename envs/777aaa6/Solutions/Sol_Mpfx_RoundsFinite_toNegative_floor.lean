-- Prove2me | solution 1 for Mpfx.RoundsFinite.toNegative_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:48.238296+00:00
-- url     : https://prove2.me/submissions/39a334a8-c6f7-4cd0-8072-4b3c33ea0d0d

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_abs_floor_le_of_abs_lt
import Theorems.Thm_Mpfx_floor_mantissa_lt
import Theorems.Thm_Mpfx_floor_minimality
import Theorems.Thm_Mpfx_mul_zpow_neg_self
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toNegative x
      (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x)) := by
  set e := F.canonicalExp x
  set c := ⌊x * (2 : ℝ) ^ (-e)⌋
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |c| ≤ (2 : ℤ) ^ p := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  obtain ⟨h_prec, h_quant, h_bnd⟩ :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_⟩
  · rw [h_y_real, ← mul_zpow_neg_self x e]
    exact mul_le_mul_of_nonneg_right (Int.floor_le _) h_2e_pos.le
  · intro z hz_mem hz_le_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    exact floor_minimality F x hz_prec hz_quant hz_le_x
end RoundsFinite
end Mpfx
