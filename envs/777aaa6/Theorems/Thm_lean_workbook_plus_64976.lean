-- Prove2me | Theorems.Thm_lean_workbook_plus_64976
-- name    : lean_workbook_plus_64976
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1fadf393-8618-4283-98fa-40dd00ed15d6
-- statement:
--   prove that $\frac{a^2}{b^2}+ \frac {b^2}{c^2}+ \frac {c^2}{a^2}+\frac {2a b c}{a^3 +b^3+c^3} \ge \frac{11}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64976 : ∀ a b c : ℝ, (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 2 * a * b * c / (a^3 + b^3 + c^3) ≥ 11 / 3)   :=  by sorry
