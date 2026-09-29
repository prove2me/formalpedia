-- Prove2me | Theorems.Thm_lean_workbook_plus_72097
-- name    : lean_workbook_plus_72097
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2658a366-f8b6-44b1-8753-82e6e1b6f6b1
-- statement:
--   Prove that $A \times B = B \times A$ if and only if $A = \oslash$ (empty set), $B = \oslash$, or $A = B$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72097 (A B : Set α) : A ×ˢ B = B ×ˢ A ↔ A = ∅ ∨ B = ∅ ∨ A = B   :=  by sorry
