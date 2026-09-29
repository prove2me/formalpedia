-- Prove2me | Theorems.Thm_lean_workbook_plus_35785
-- name    : lean_workbook_plus_35785
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/aad3d669-fa24-4ae7-bd4f-c29e31a0a796
-- statement:
--   Correct solution: We'll first find the amount that's a multiple of $4$ or $6$ . From PIE, this is $250+166-83$ . Now we subtract off the amount that is a multiple of $24$ , or $41$ . This makes the answer $250+166-83-41 = \boxed{292}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35785 :
  Finset.card (Finset.filter (λ x => 4 ∣ x ∨ 6 ∣ x) (Finset.Icc 1 1000)) -
      Finset.card (Finset.filter (λ x => 24 ∣ x) (Finset.Icc 1 1000)) = 292   :=  by sorry
