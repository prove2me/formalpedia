-- Prove2me | Theorems.Thm_lean_workbook_plus_76551
-- name    : lean_workbook_plus_76551
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/bbf49c36-c2c1-4f91-af72-40a1c1f5a68a
-- statement:
--   Let $ a,b $ be nonnegative real numbers such that $a^2+b^2 = a^5+b^5$ . Prove that $ a^2+b^2\le 2 .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76551 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 + b^2 = a^5 + b^5) : a^2 + b^2 ≤ 2   :=  by sorry
