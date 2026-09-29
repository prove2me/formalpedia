-- Prove2me | Theorems.Thm_lean_workbook_plus_78814
-- name    : lean_workbook_plus_78814
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2b5cfa23-f69e-464a-af71-78e90f74ebd6
-- statement:
--   The (much) simpler way to count is $\left \lfloor \frac {999} {6} \right \rfloor - \left \lfloor \frac {99} {6} \right \rfloor = 166 - 16 = 150$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78814 :
  Finset.card (Finset.filter (λ x => 6∣x) (Finset.Icc 1 999)) - Finset.card (Finset.filter (λ x => 6∣x) (Finset.Icc 1 99)) = 150   :=  by sorry
