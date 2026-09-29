-- Prove2me | Theorems.Thm_lean_workbook_plus_3637
-- name    : lean_workbook_plus_3637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/189ef7a0-e56c-4ba1-976c-9d1a5db5c189
-- statement:
--   Prove that $5(\sum_{cyc} a^2)^2\geq 3\sum_{cyc} a^2bc+4(\sum_{cyc} a^2)(\sum_{cyc} ab)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3637 (a b c : ℝ) :
  5 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) + 4 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)   :=  by sorry
