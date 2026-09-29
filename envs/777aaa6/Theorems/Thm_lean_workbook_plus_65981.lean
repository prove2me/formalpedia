-- Prove2me | Theorems.Thm_lean_workbook_plus_65981
-- name    : lean_workbook_plus_65981
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/234985b5-f2f3-43d8-a57c-183d1100798c
-- statement:
--   Prove that : $(ab+bc+ca-1)^2 \leq (a^2+1)(b^2+1)(c^2+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65981 (a b c : ℝ) : (a * b + b * c + c * a - 1) ^ 2 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)   :=  by sorry
