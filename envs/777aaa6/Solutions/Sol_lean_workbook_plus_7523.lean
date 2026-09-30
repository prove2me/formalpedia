-- Prove2me | solution 1 for lean_workbook_plus_7523
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:58.268869+00:00
-- url     : https://prove2.me/submissions/51eed8fa-1e2f-4666-b689-8cba969510ac

import Mathlib.Analysis.Complex.Basic

theorem solution  (x y : ℤ)
  (h₀ : x * y ≡ 1 [ZMOD 2]) :
  x % 2 = 1 ∧ y % 2 = 1 := by
  have h : x * y % 2 = 1 := h₀
  rw [Int.mul_emod] at h
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
  rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
  simp [hx, hy] at h ⊢
