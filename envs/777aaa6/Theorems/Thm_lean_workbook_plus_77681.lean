-- Prove2me | Theorems.Thm_lean_workbook_plus_77681
-- name    : lean_workbook_plus_77681
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ada7ea4e-318f-4d34-b5e9-c25dd8c01573
-- statement:
--   Let $a,b,c > 0 $. Prove that $2(\sum a)^{6}-12(\sum a)^{4}\sum ab+9abc(\sum a)^{3}+27(\sum a)^{2}(\sum ab)^{2}+243a^{2}b^{2}c^{2}+324abc(\sum a)(\sum ab)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77681 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a + b + c) ^ 6 - 12 * (a + b + c) ^ 4 * (a * b + b * c + c * a) + 9 * a * b * c * (a + b + c) ^ 3 + 27 * (a + b + c) ^ 2 * (a * b + b * c + c * a) ^ 2 + 243 * a ^ 2 * b ^ 2 * c ^ 2 + 324 * a * b * c * (a + b + c) * (a * b + b * c + c * a) ≥ 0   :=  by sorry
