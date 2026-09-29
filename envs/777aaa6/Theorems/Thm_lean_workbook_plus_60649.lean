-- Prove2me | Theorems.Thm_lean_workbook_plus_60649
-- name    : lean_workbook_plus_60649
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/82908a50-652a-4926-8bb0-7ca0a574a043
-- statement:
--   Prove the inequality $|xy|\leq\frac{1}{2}(|x|^2 + |y|^2)$ for complex numbers $x$ and $y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60649 (x y : ℂ) : ‖x * y‖ ≤ (1 / 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2)   :=  by sorry
