-- Prove2me | Theorems.Thm_lean_workbook_plus_82238
-- name    : lean_workbook_plus_82238
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6a2d93ae-5249-48d3-aba7-e02d6846307e
-- statement:
--   Prove that : $F'(x) = \frac {1}{x} - \ln{(1 + \frac {1}{x})} \geq 0$ for $x \geq 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82238 (x : ℝ) (hx : 5 ≤ x) : (1 / x - Real.log (1 + 1 / x)) ≥ 0   :=  by sorry
