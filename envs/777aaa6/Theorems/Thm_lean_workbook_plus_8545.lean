-- Prove2me | Theorems.Thm_lean_workbook_plus_8545
-- name    : lean_workbook_plus_8545
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7d29b00e-46a5-441d-95fb-80ee3c2add49
-- statement:
--   Prove that $(a+b+c)^2 \geq 3(ab+bc+ca)$ for all positive real numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8545 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)   :=  by sorry
