-- Prove2me | Theorems.Thm_lean_workbook_plus_46094
-- name    : lean_workbook_plus_46094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0163eb76-a48f-4363-b4d9-57f0e816d180
-- statement:
--   Assume that $|a_i-a_j|+|b_i-b_j|>1 \forall i \neq j \leq 7$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46094 (a b : Fin 7 → ℝ) (h : ∀ i j, i ≠ j → 1 < |a i - a j| + |b i - b j|) : 1 < |a 0 - a 1| + |b 0 - b 1| ∧ 1 < |a 1 - a 2| + |b 1 - b 2| ∧ 1 < |a 2 - a 3| + |b 2 - b 3| ∧ 1 < |a 3 - a 4| + |b 3 - b 4| ∧ 1 < |a 4 - a 5| + |b 4 - b 5| ∧ 1 < |a 5 - a 6| + |b 5 - b 6| ∧ 1 < |a 6 - a 7| + |b 6 - b 7|   :=  by sorry
