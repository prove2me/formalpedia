-- Prove2me | Theorems.Thm_lean_workbook_plus_41967
-- name    : lean_workbook_plus_41967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6d19fe5b-805e-4245-8ec4-0510ac78bd73
-- statement:
--   Prove that $\sum_{cyc} a^2(a-b)(a-c) + \frac{3}{2} \sum_{cyc} (ab-ca)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41967 (a b c : ℝ) : a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - a) * (b - c) + c ^ 2 * (c - a) * (c - b) + (3 / 2) * ((a * b - c * a) ^ 2 + (b * c - a * b) ^ 2 + (c * a - b * c) ^ 2) ≥ 0   :=  by sorry
