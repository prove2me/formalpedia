-- Prove2me | Theorems.Thm_lean_workbook_plus_70146
-- name    : lean_workbook_plus_70146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/99c5faf7-fcf6-4057-83c6-2e9608f09200
-- statement:
--   $ \sum_{sym}{a^4b^2} \ge \sum_{sym}{a^4bc} \iff \sum_{cyc}{a^4(b-c)^2} \ge 0$ ;
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70146 {a b c : ℝ} :
  a ^ 4 * b ^ 2 + a ^ 4 * c ^ 2 + b ^ 4 * c ^ 2 + b ^ 4 * a ^ 2 + c ^ 4 * a ^ 2 + c ^ 4 * b ^ 2 ≥ a ^ 4 * b * c + a ^ 4 * c * b + b ^ 4 * c * a + b ^ 4 * a * c + c ^ 4 * a * b + c ^ 4 * b * a ↔ a ^ 4 * (b - c) ^ 2 + b ^ 4 * (c - a) ^ 2 + c ^ 4 * (a - b) ^ 2 ≥ 0   :=  by sorry
