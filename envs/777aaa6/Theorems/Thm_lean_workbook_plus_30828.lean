-- Prove2me | Theorems.Thm_lean_workbook_plus_30828
-- name    : lean_workbook_plus_30828
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/92a556ee-0794-49df-8354-d8365322d57c
-- statement:
--   Let $a,b,c\in [\frac{1}{2},2 ]$ , prove or disprove : $9\le(a+b+c)(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})\le10 .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30828 : ∀ a b c : ℝ, a ∈ Set.Icc (1 / 2) 2 ∧ b ∈ Set.Icc (1 / 2) 2 ∧ c ∈ Set.Icc (1 / 2) 2 → 9 ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) ∧ (a + b + c) * (1 / a + 1 / b + 1 / c) ≤ 10   :=  by sorry
