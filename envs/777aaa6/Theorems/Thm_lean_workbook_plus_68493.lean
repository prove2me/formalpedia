-- Prove2me | Theorems.Thm_lean_workbook_plus_68493
-- name    : lean_workbook_plus_68493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/9eb2e03b-4b64-43c3-92dd-0d9b1482e407
-- statement:
--   Prove that $\sum a^2\geqslant \frac{(\sum a)^2}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68493 (a b c: ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ (a + b + c) ^ 2 / 4   :=  by sorry
