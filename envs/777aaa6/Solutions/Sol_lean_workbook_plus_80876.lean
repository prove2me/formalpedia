-- Prove2me | solution 1 for lean_workbook_plus_80876
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:56:13.150631+00:00
-- url     : https://prove2.me/submissions/1af6d977-04a6-48ef-b6e0-84e04790a3ba

import Mathlib.Tactic

theorem solution (b c p : ℝ) (h₁ : -b^2 + c^2 + p^2 = 2 * p^2) : -b^2 + c^2 = p^2 := by linarith
