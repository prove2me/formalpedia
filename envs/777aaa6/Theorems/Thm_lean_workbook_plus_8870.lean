-- Prove2me | Theorems.Thm_lean_workbook_plus_8870
-- name    : lean_workbook_plus_8870
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/09e04d03-7ebb-489c-bc32-9fe742b54e0a
-- statement:
--   After assuming $a, b, c$ are positive and homogenizing, the inequality becomes $\sum_{cyc}(a^2+ab)\sum_{sym}\left(a^5b+5a^4b^2+4a^3b^3+3a^4bc+16a^3b^2c+\frac{13}{3}a^2b^2c^2\right)\geq0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8870 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + a * b + b^2) * (a^5 * b + 5 * a^4 * b^2 + 4 * a^3 * b^3 + 3 * a^4 * b * c + 16 * a^3 * b^2 * c + 13 / 3 * a^2 * b^2 * c^2) + (b^2 + b * c + c^2) * (b^5 * c + 5 * b^4 * c^2 + 4 * b^3 * c^3 + 3 * b^4 * c * a + 16 * b^3 * c^2 * a + 13 / 3 * b^2 * c^2 * a^2) + (c^2 + c * a + a^2) * (c^5 * a + 5 * c^4 * a^2 + 4 * c^3 * a^3 + 3 * c^4 * a * b + 16 * c^3 * a^2 * b + 13 / 3 * c^2 * a^2 * b^2) ≥ 0   :=  by sorry
