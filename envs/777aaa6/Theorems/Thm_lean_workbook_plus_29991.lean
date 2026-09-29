-- Prove2me | Theorems.Thm_lean_workbook_plus_29991
-- name    : lean_workbook_plus_29991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b22a01df-203c-4fad-860f-195a6c553a92
-- statement:
--   If $A\cup B=A\cup C$ & $A\cap B=A\cap C$ prove that $B=C$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29991 {α : Type} (A B C : Set α) (h1 : A ∪ B = A ∪ C) (h2 : A ∩ B = A ∩ C) : B = C   :=  by sorry
