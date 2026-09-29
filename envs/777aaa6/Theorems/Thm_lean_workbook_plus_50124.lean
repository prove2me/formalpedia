-- Prove2me | Theorems.Thm_lean_workbook_plus_50124
-- name    : lean_workbook_plus_50124
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e2ab1e2f-9ffb-4d46-91b7-309bb893fd80
-- statement:
--   Prove that $a^{4} + b^{4} + 2 \geq 4ab$ for $a, b \in R^+$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50124 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^4 + b^4 + 2 ≥ 4 * a * b   :=  by sorry
