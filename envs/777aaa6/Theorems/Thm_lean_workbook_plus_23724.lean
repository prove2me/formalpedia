-- Prove2me | Theorems.Thm_lean_workbook_plus_23724
-- name    : lean_workbook_plus_23724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/46f1ab28-fc70-472a-9733-5b939773080e
-- statement:
--   Find the points of equality for the inequality $ (a - b)^2(a - c)^2(b - c)^2 \ge 0 $ where $ a, b, c \ge 0 $ with $ a + b + c = 3 $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23724 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) :  (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 ≥ 0   :=  by sorry
