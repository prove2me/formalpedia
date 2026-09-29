-- Prove2me | Theorems.Thm_lean_workbook_plus_66314
-- name    : lean_workbook_plus_66314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/49e697f4-fb80-4daf-9ae3-a547121fb340
-- statement:
--   Let $ a$ and $ b$ be nonnegative real numbers. If $ 2a^2 + b^2 = 2a + b$ , then $ 1 - ab\ge \frac {a - b}{3}$ ;
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66314 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * a ^ 2 + b ^ 2 = 2 * a + b) : 1 - a * b ≥ (a - b) / 3   :=  by sorry
