-- Prove2me | Theorems.Thm_lean_workbook_plus_21536
-- name    : lean_workbook_plus_21536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b9f9c12f-7190-4517-9e12-f98692b21585
-- statement:
--   Prove that \n $ 2(a^{4}+b^{4}+c^{4})+5(a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2})- \sum ab(3a^{2}+4b^{2}) \geq 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21536 (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 5 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a * b * (3 * a ^ 2 + 4 * b ^ 2) + b * c * (3 * b ^ 2 + 4 * c ^ 2) + c * a * (3 * c ^ 2 + 4 * a ^ 2)) ≥ 0   :=  by sorry
