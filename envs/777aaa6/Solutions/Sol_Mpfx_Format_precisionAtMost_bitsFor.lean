-- Prove2me | solution 1 for Mpfx.Format.precisionAtMost_bitsFor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:29:18.828082+00:00
-- url     : https://prove2.me/submissions/c4c4bbcb-be2d-4474-a71a-7d965a3bc227

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_abs_mul_two_zpow


set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution {x : Dyadic} {m : ℤ} {B : ℝ}
    (hq : Dyadic.quantumAtLeast (m : QExp) x) (hb : |(x : ℝ)| ≤ B) :
    Dyadic.precisionAtMost (bitsFor B m : Prec) x := by
  obtain ⟨c, hc⟩ := (Dyadic.quantumAtLeast_coe_real m x).mp hq
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) _
  have h_c_le_ratio : |(c : ℝ)| ≤ B / (2 : ℝ) ^ m := by
    rw [le_div_iff₀ h2m_pos, ← abs_mul_two_zpow, ← hc]
    exact hb
  have h_floor_nn : 0 ≤ ⌊B / (2 : ℝ) ^ m⌋ :=
    Int.floor_nonneg.mpr ((abs_nonneg _).trans h_c_le_ratio)
  set N : ℕ := Int.toNat ⌊B / (2 : ℝ) ^ m⌋ with hN_def
  have h_abs_c_le : |c| ≤ (N : ℤ) := by
    rw [hN_def, Int.toNat_of_nonneg h_floor_nn]
    exact Int.le_floor.mpr (by rw [Int.cast_abs]; exact h_c_le_ratio)
  refine (Dyadic.precisionAtMost_coe_real _ x).mpr ⟨c, m, hc, ?_⟩
  have h_natAbs_le : c.natAbs ≤ N := by
    have : (c.natAbs : ℤ) ≤ (N : ℤ) := by rw [Int.natCast_natAbs]; exact h_abs_c_le
    exact_mod_cast this
  have h_clog : N + 1 ≤ 2 ^ Nat.clog 2 (N + 1) := Nat.le_pow_clog (by norm_num : 1 < 2) _
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Nat.lt_of_lt_of_le (by omega : c.natAbs < N + 1) h_clog
end Mpfx.Format
