-- Prove2me | solution 1 for Mpfx.abs_floor_add_one_le_of_abs_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:44.177978+00:00
-- url     : https://prove2.me/submissions/c301a767-bbb0-444b-a8e8-abe990ee517f

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {r : ℝ} {p : ℕ}
    (h : |r| < (2 : ℝ) ^ p) :
    |⌊r⌋ + 1| ≤ (2 : ℤ) ^ p := by
  obtain ⟨h_neg_lt, h_lt⟩ := abs_lt.mp h
  have h_lo_upper : ⌊r⌋ ≤ (2 : ℤ) ^ p - 1 := by
    have h1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le _
    have h2 : (⌊r⌋ : ℝ) < (2 : ℝ) ^ p := lt_of_le_of_lt h1 h_lt
    have : (⌊r⌋ : ℤ) < ((2 : ℤ) ^ p : ℤ) := by exact_mod_cast h2
    omega
  have h_lo_lower : -((2 : ℤ) ^ p) ≤ ⌊r⌋ := by
    have h_floor_succ : r < (⌊r⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h_lo_lower_r : -((2 : ℝ) ^ p) < (⌊r⌋ : ℝ) + 1 := by linarith
    have : -((2 : ℤ) ^ p) < ⌊r⌋ + 1 := by exact_mod_cast h_lo_lower_r
    omega
  rw [abs_le]; exact ⟨by linarith, by linarith⟩
end Mpfx
