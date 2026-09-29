-- Prove2me | Theorems.Thm_lean_workbook_plus_16958
-- name    : lean_workbook_plus_16958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d61085db-8c11-46aa-b1f0-e948dbdf6980
-- statement:
--   Prove that $a^2-ab+b^2=(a+b)^2-3ab \ge \frac{(a+b)^2}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16958 (a b : ℝ) : (a + b) ^ 2 - 3 * a * b ≥ (a + b) ^ 2 / 4   :=  by sorry
