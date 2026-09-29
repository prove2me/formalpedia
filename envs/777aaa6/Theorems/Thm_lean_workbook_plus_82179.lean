-- Prove2me | Theorems.Thm_lean_workbook_plus_82179
-- name    : lean_workbook_plus_82179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1c24f716-bc63-45d6-a292-4bfdec278b8e
-- statement:
--   Prove that if $a,b,c>0$ then \n $ (a^2+b^2+c^2)^2+(ab+bc+ca)^2\geq 2(a^2+b^2+c^2)(ab+bc+ca). $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82179 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a^2+b^2+c^2)^2 + (a*b+b*c+c*a)^2 ≥ 2 * (a^2+b^2+c^2) * (a*b+b*c+c*a)   :=  by sorry
