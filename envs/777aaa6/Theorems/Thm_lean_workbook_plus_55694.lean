-- Prove2me | Theorems.Thm_lean_workbook_plus_55694
-- name    : lean_workbook_plus_55694
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/939f237d-6c91-4b34-bdbd-0c2ea47c88d8
-- statement:
--   Prove that $ A\cap (B-C)=(A\cap B)-(A\cap C) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55694 (A B C : Set α) : A ∩ (B \ C) = (A ∩ B) \ (A ∩ C)   :=  by sorry
