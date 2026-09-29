-- Prove2me | solution 1 for fermat_little_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:57.791559+00:00
-- url     : https://prove2.me/submissions/1504fffc-72ee-4581-a22c-ce878653387d

import Theorems.Thm_fermat_little_7
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) : (7 : ℤ) ∣ a ^ 7 - a := by
  have key : ∀ x : ZMod 7, x ^ 7 - x = 0 := by decide
  have h : ((a ^ 7 - a : ℤ) : ZMod 7) = 0 := by push_cast; exact key _
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
