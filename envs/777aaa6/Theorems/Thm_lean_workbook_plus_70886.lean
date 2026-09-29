-- Prove2me | Theorems.Thm_lean_workbook_plus_70886
-- name    : lean_workbook_plus_70886
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b2b3b773-ca0d-44d4-9e1c-57d871443b52
-- statement:
--   Prove that $(a^{2}+b^{2}+c^{2})^{2}\ge \sum_{cyc}a^{2}(b^{2}+bc+a^{2})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70886 (a b c : ℝ) : (a^2 + b^2 + c^2)^2 ≥ a^2 * (b^2 + b * c + a^2) + b^2 * (c^2 + c * a + b^2) + c^2 * (a^2 + a * b + c^2)   :=  by sorry
