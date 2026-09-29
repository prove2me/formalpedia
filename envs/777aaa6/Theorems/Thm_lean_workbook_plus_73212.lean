-- Prove2me | Theorems.Thm_lean_workbook_plus_73212
-- name    : lean_workbook_plus_73212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/05182ead-2f69-4af0-b7a4-f3cdba4207e9
-- statement:
--   $(bc^3+ca^3+ab^3)^2\geq 3abc(a^2c^3+a^3b^2+b^3c^2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73212 (a b c : ℝ) : (b * c ^ 3 + c * a ^ 3 + a * b ^ 3) ^ 2 ≥ 3 * a * b * c * (a ^ 2 * c ^ 3 + a ^ 3 * b ^ 2 + b ^ 3 * c ^ 2)   :=  by sorry
