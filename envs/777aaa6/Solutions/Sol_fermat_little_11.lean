-- Prove2me | solution 1 for fermat_little_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:58.481782+00:00
-- url     : https://prove2.me/submissions/f15fca78-dffc-4969-9407-1e4cd716c70d

import Theorems.Thm_fermat_little_11
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) : (11 : ℤ) ∣ a ^ 11 - a := by
  have key : ∀ x : ZMod 11, x ^ 11 - x = 0 := by decide
  have h : ((a ^ 11 - a : ℤ) : ZMod 11) = 0 := by push_cast; exact key _
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
