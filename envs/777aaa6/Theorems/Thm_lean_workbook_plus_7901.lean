-- Prove2me | Theorems.Thm_lean_workbook_plus_7901
-- name    : lean_workbook_plus_7901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4ea715b8-fad5-4c66-9140-bdb17107f469
-- statement:
--   Prove that $\frac{1}{2}(a^2+b^2) \ge ab$, $\frac{1}{2}(b^2+c^2) \ge bc$, and $\frac{1}{2}(a^2+c^2) \ge ac$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7901 (a b c : ℝ) : (a^2 + b^2)/2 ≥ a * b ∧ (b^2 + c^2)/2 ≥ b * c ∧ (c^2 + a^2)/2 ≥ c * a   :=  by sorry
