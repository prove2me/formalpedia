-- Prove2me | Theorems.Thm_lean_workbook_plus_20129
-- name    : lean_workbook_plus_20129
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4a564f79-981f-4a0f-9408-16241c9b005c
-- statement:
--   Let $a_1,a_2 ,\cdots ,a_n \in (0,1)$ , prove that $\sqrt{a_1a_2\cdots a_n}+\sqrt{(1-a_1)(1-a_2)\cdots (1-a_n)}<1.$ $(n\ge 2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20129 : ∀ n : ℕ, 2 ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 < a i ∧ a i < 1) → Real.sqrt (∏ i, a i) + Real.sqrt (∏ i, (1 - a i)) < 1   :=  by sorry
