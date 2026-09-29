-- Prove2me | Theorems.Thm_lean_workbook_plus_384
-- name    : lean_workbook_plus_384
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/92d57e98-4e3f-4f60-9be4-b05d61211816
-- statement:
--   Prove that for positive real numbers $a, b, c$:\n$$2(a^4+b^4+c^4)+4(a^2b^2+c^2a^2+b^2c^2) \ge 3(a^3c+b^3a+c^3b)+3abc(a+b+c)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_384 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) + 3 * a * b * c * (a + b + c)   :=  by sorry
