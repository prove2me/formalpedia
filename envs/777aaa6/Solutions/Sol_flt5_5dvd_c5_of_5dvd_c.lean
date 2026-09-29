-- Prove2me | solution 1 for flt5_5dvd_c5_of_5dvd_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:25:22.219544+00:00
-- url     : https://prove2.me/submissions/b524f3e7-6461-4d3a-b384-b766c828af21

import Theorems.Thm_flt5_5dvd_c5_of_5dvd_c
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (c : ℤ) (h5c : (5 : ℤ) ∣ c) : (5 : ℤ) ∣ c ^ 5 := by
  obtain ⟨k, hk⟩ := h5c
  exact ⟨5 ^ 4 * k ^ 5, by rw [hk]; ring⟩
