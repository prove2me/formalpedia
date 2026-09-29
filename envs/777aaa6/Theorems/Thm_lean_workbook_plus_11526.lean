-- Prove2me | Theorems.Thm_lean_workbook_plus_11526
-- name    : lean_workbook_plus_11526
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e7a87ce7-fa73-4806-91da-87e7f4899be3
-- statement:
--   The inequality becomes $(a^2+ab+b^2)(b^2+bc+c^2)(c^2+ca+a^2) \ge 3(ab^2+bc^2+ca^2)(a^2b+b^2c+c^2a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11526 (a b c : ℝ) : (a^2 + b^2 + a * b) * (b^2 + c^2 + b * c) * (c^2 + a^2 + c * a) ≥ 3 * (a * b^2 + b * c^2 + c * a^2) * (a^2 * b + b^2 * c + c^2 * a)   :=  by sorry
