-- Prove2me | Theorems.Thm_lean_workbook_plus_3670
-- name    : lean_workbook_plus_3670
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/829d2370-2e05-4a41-8aed-27e58f0f50f6
-- statement:
--   Prove that for all positive real numbers $a$ and $ b$ : $\frac{(a + b)^3}{4} \ge a^2b + ab^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3670 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 3 / 4 ≥ a ^ 2 * b + a * b ^ 2   :=  by sorry
