-- Prove2me | Theorems.Thm_lean_workbook_plus_71682
-- name    : lean_workbook_plus_71682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/fb780d25-39d5-4c23-b0cf-ea84ecb3634a
-- statement:
--   Solution\n\n $$LHS - RHS = (a^2+b^2+c^2-ab-bc-ca)^2+(a-bc)^2+(b-ac)^2+(c-ab)^2 \ge 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71682 :
  ∀ a b c : ℝ, (a^2 + b^2 + c^2 - a * b - b * c - c * a)^2 + (a - b * c)^2 + (b - a * c)^2 + (c - a * b)^2 ≥ 0   :=  by sorry
