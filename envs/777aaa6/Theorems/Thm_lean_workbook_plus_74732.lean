-- Prove2me | Theorems.Thm_lean_workbook_plus_74732
-- name    : lean_workbook_plus_74732
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ffe4763f-125a-47a6-b154-ecca97192772
-- statement:
--   $$\frac{x}{y + 3} +\frac{ 2y}{x +1} \ge \frac{1}5 \iff 4{{x}^{2}}-12x+9\ge 0 $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74732 : ∀ x y : ℝ, (x / (y + 3) + 2 * y / (x + 1) ≥ 1 / 5 ↔ 4 * x ^ 2 - 12 * x + 9 ≥ 0)   :=  by sorry
