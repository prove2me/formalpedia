-- Prove2me | solution 1 for P2M_Mpfx_nearest_eq_of_close__390f66b23c83
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:28:13.818835+00:00
-- url     : https://prove2.me/submissions/b797963f-4fbd-4ef5-8b6f-6a7ff86dd0cb

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_nearest_eq_of_close
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_inj



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (tb : TieBreak) (v : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) {g : _root_.Mpfx.Dyadic}
    (hg : _root_.Mpfx.Dyadic.quantumAtLeast ((F.canonicalExp v : ℤ) : QExp) g)
    (hclose : |v - (g : ℝ)| < (2 : ℝ) ^ (F.canonicalExp v) / 2) :
    RoundsFinite F.unbounded (.nearest tb) v g := by
  obtain ⟨m, hm⟩ := (Dyadic.quantumAtLeast_coe_real (F.canonicalExp v) g).mp hg
  have hgeq : Dyadic.ofIntZpow m (F.canonicalExp v) = g :=
    (Dyadic.coe_real_inj _ _).mp (by rw [Dyadic.coe_ofIntZpow, hm])
  rw [← hgeq]
  refine nearest_eq_of_close F tb v hundef ?_
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(F.canonicalExp v)) := zpow_pos (by norm_num) _
  have hrw : v * (2 : ℝ) ^ (-(F.canonicalExp v)) - (m : ℝ)
      = (v - (g : ℝ)) * (2 : ℝ) ^ (-(F.canonicalExp v)) := by
    rw [hm, sub_mul, mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel,
        zpow_zero, mul_one]
  rw [hrw, abs_mul, abs_of_pos h2pos]
  have hcc : (2 : ℝ) ^ (F.canonicalExp v) * (2 : ℝ) ^ (-(F.canonicalExp v)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  calc |v - (g : ℝ)| * (2 : ℝ) ^ (-(F.canonicalExp v))
      < (2 : ℝ) ^ (F.canonicalExp v) / 2 * (2 : ℝ) ^ (-(F.canonicalExp v)) :=
        mul_lt_mul_of_pos_right hclose h2pos
    _ = 1 / 2 := by rw [div_mul_eq_mul_div, hcc]
end Mpfx
