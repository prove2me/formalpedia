-- Prove2me | Theorems.Thm_lean_workbook_plus_37567
-- name    : lean_workbook_plus_37567
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/636463b4-6ae5-4c3b-afa2-c3d234ed7691
-- statement:
--   Let $a,b,c\geq 0,a^2+b^2+c^2>0$ .Prove that $\dfrac{1}{4b^2+4c^2-bc}+\dfrac{1}{4c^2+4a^2-ac}+\dfrac{1}{4a^2+4b^2-ab}\geq \dfrac{9}{7\left(a^2+b^2+c^2\right)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37567 :  ∀ a b c : ℝ, a ≥ b ∧ b ≥ c ∧ c ≥ 0 ∧ a^2 + b^2 + c^2 > 0 →   1 / (4 * b^2 + 4 * c^2 - b * c) + 1 / (4 * c^2 + 4 * a^2 - a * c) + 1 / (4 * a^2 + 4 * b^2 - a * b) ≥ 9 / (7 * (a^2 + b^2 + c^2))   :=  by sorry
