-- Prove2me | Theorems.Thm_lean_workbook_plus_71904
-- name    : lean_workbook_plus_71904
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3064d3e7-11df-4f1a-b104-52d4f6e51f2a
-- statement:
--   $(a-b)^5+(b-c)^5+(c-a)^5=5(a-b)(b-c)(c-a)\left(a^2+b^2+c^2-ab-bc-ca\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71904 (a b c : ℝ) : (a - b) ^ 5 + (b - c) ^ 5 + (c - a) ^ 5 = 5 * (a - b) * (b - c) * (c - a) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a)   :=  by sorry
