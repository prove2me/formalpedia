-- Prove2me | Theorems.Thm_lean_workbook_plus_9685
-- name    : lean_workbook_plus_9685
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d3c801b6-6108-43f5-b181-bae13e43b0ce
-- statement:
--   Prove that $25+6(\sqrt{\frac {p}{q}}-\sqrt{\frac{q}{p}})^2 \ge 25.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9685 : ∀ p q : ℝ, p > 0 ∧ q > 0 → 25 + 6 * (Real.sqrt (p / q) - Real.sqrt (q / p)) ^ 2 ≥ 25   :=  by sorry
