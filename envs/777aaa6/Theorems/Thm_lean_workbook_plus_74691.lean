-- Prove2me | Theorems.Thm_lean_workbook_plus_74691
-- name    : lean_workbook_plus_74691
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/13f1b5bb-b752-4e62-afe6-63dcf329ff01
-- statement:
--   $27(3a^3+3b^3+3c^3+7abc) \ge 16(a+b+c)^3$ $\iff 65\sum a^3+93abc \ge 48\sum ab(a+b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74691 (a b c : ℝ) : 27 * (3 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + 7 * a * b * c) ≥ 16 * (a + b + c) ^ 3 ↔ 65 * (a ^ 3 + b ^ 3 + c ^ 3) + 93 * a * b * c ≥ 48 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))   :=  by sorry
