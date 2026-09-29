-- Prove2me | Theorems.Thm_lean_workbook_plus_47834
-- name    : lean_workbook_plus_47834
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/23ad60d8-589b-47f0-9d57-41796b0d5cf9
-- statement:
--   Let $ a,b $ be nonnegative real numbers such that $a^2+b^2 = a^5+b^5$ . Prove that $ a+b\le 2 .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47834 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 + b^2 = a^5 + b^5) : a + b ≤ 2   :=  by sorry
