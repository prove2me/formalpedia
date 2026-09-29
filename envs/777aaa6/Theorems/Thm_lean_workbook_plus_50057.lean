-- Prove2me | Theorems.Thm_lean_workbook_plus_50057
-- name    : lean_workbook_plus_50057
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c53223e9-a1b9-4363-bb71-682edef6fa75
-- statement:
--   Prove the set equality for a general case: $(X \times Y)-(X^\prime \times Y^\prime) = [(X \cap X^\prime) \times (Y - Y^\prime)] \cup [(X - X^\prime) \times Y]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50057 (X X' Y Y' : Set α) : (X ×ˢ Y) \ (X' ×ˢ Y') = (X ∩ X') ×ˢ (Y \ Y') ∪ (X \ X') ×ˢ Y   :=  by sorry
