-- Prove2me | Theorems.Thm_lean_workbook_plus_14479
-- name    : lean_workbook_plus_14479
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/018007d3-4da8-4652-86c4-35a1a06ea74a
-- statement:
--   Note that since $K=\dfrac12ab\sin C$ we have $\sqrt{a^2b^2-4K^2}=\sqrt{a^2b^2-4\left(\dfrac14a^2b^2\sin^2C\right)}=ab\sqrt{1-\sin^2C}=ab\cos C.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14479 :
  ∀ a b c K : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ K > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a ∧ a^2 + b^2 + c^2 = 2 * (a * b + b * c + c * a) →
  Real.sqrt (a^2 * b^2 - 4 * K^2) = a * b * Real.cos c   :=  by sorry
