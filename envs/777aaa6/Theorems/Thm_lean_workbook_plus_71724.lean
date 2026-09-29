-- Prove2me | Theorems.Thm_lean_workbook_plus_71724
-- name    : lean_workbook_plus_71724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/608a0d84-bfc6-4220-8b13-b5aef460d877
-- statement:
--   Let $x,y \in \mathbb{R}$ such that $x+y = 2$ . Prove that $xy(x^2+y^2) \le 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71724 (x y : ℝ) (h : x + y = 2) : x * y * (x ^ 2 + y ^ 2) ≤ 2   :=  by sorry
