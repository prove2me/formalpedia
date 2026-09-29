-- Prove2me | Theorems.Thm_lean_workbook_plus_963
-- name    : lean_workbook_plus_963
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d8d28a51-91fc-4164-81b3-b4351f1420a1
-- statement:
--   Prove that $[(A\cup B)\cap (A\cap C)]\cap B^{c}=(A\setminus B)\setminus C^{c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_963 : ∀ A B C : Set α, ((A ∪ B) ∩ (A ∩ C)) ∩ Bᶜ = (A \ B) \ Cᶜ   :=  by sorry
