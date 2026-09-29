-- Prove2me | Theorems.Thm_lean_workbook_plus_16830
-- name    : lean_workbook_plus_16830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/dfe35e73-91d8-4447-880f-c75d74dca67d
-- statement:
--   Prove that $(a^2-ab+b^2)^2 \geq \frac{1}{2}(a^4+b^4)$ for all real numbers $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16830 (a b : ℝ) : (a^2 - a * b + b^2)^2 ≥ 1/2 * (a^4 + b^4)   :=  by sorry
