-- Prove2me | Theorems.Thm_lean_workbook_plus_54450
-- name    : lean_workbook_plus_54450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/5e8a561a-9f8f-4482-bfd7-7e91f724c056
-- statement:
--   Prove that \n $(a^2+b^2)(b^2+c^2)(c^2+a^2)\geq 2(ab^2+bc^2+ca^2-abc)(a^2b+b^2c+c^2a-abc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54450 (a b c : ℝ) : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ 2 * (a * b^2 + b * c^2 + c * a^2 - a * b * c) * (a^2 * b + b^2 * c + c^2 * a - a * b * c)   :=  by sorry
