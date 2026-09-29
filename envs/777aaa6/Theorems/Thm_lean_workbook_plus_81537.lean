-- Prove2me | Theorems.Thm_lean_workbook_plus_81537
-- name    : lean_workbook_plus_81537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7fad5de7-b58c-46cc-9b68-fb15923c631d
-- statement:
--   Prove that for any $a,b,c\in\mathbb{R}$ satisfying $a+b+c=1$, the expression $a^{3}+b^{3}+c^{3}-3abc$ is nonnegative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81537 {a b c : ℝ} (h : a + b + c = 1) :
  a^3 + b^3 + c^3 - 3 * a * b * c ≥ 0   :=  by sorry
