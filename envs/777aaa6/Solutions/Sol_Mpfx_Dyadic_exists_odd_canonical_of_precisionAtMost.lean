-- Prove2me | solution 1 for Mpfx.Dyadic.exists_odd_canonical_of_precisionAtMost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:32:44.555758+00:00
-- url     : https://prove2.me/submissions/74775041-496e-4fc0-9978-0aca8cdbb56b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local norm_cast] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local norm_cast] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local norm_cast] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local norm_cast] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local norm_cast] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local norm_cast] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff
section
namespace Mpfx
namespace IsDyadic
end IsDyadic
namespace Dyadic
private theorem Int.exists_odd_factor {c₀ : ℤ} (hc : c₀ ≠ 0) :
    ∃ k : ℕ, ∃ c : ℤ, Odd c ∧ c₀ = c * 2^k ∧ c.natAbs ≤ c₀.natAbs := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hc)
  have hm_le : m ≤ c₀.natAbs := hn ▸ Nat.le_mul_of_pos_left m (by positivity)
  rcases Int.natAbs_eq c₀ with h | h
  · exact ⟨k, m, (Int.odd_coe_nat m).mpr hm, by rw [h, hn]; push_cast; ring, by simpa using hm_le⟩
  · exact ⟨k, -m, ((Int.odd_coe_nat m).mpr hm).neg, by rw [h, hn]; push_cast; ring,
      by simpa using hm_le⟩
end Dyadic
namespace Dyadic
end Dyadic
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {p : ℕ} {y : Dyadic}
    (hp : precisionAtMost (p : Prec) y) (hy : (y : ℝ) ≠ 0) :
    ∃ c e : ℤ, ((y : ℝ) = c * (2 : ℝ)^e) ∧ Odd c ∧ |c| < (2 : ℤ)^p := by
  rw [precisionAtMost_coe_real] at hp
  obtain ⟨c₀, e₀, hy_eq, hc₀_lt⟩ := hp
  have hc₀_ne : c₀ ≠ 0 := by
    intro h; rw [h] at hy_eq; push_cast at hy_eq
    rw [zero_mul] at hy_eq; exact hy hy_eq
  obtain ⟨k, c, h_odd, hc_eq, h_natAbs⟩ := Int.exists_odd_factor hc₀_ne
  refine ⟨c, e₀ + k, ?_, h_odd, ?_⟩
  · rw [hy_eq, hc_eq]
    push_cast
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    ring
  · -- |c| ≤ |c₀| < 2^p.
    have hc_le : |c| ≤ |c₀| := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      exact_mod_cast h_natAbs
    linarith
end Mpfx.Dyadic
