-- Prove2me | Theorems.Thm_lean_workbook_plus_76520
-- name    : lean_workbook_plus_76520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/7d19a6e6-9ca7-4bc0-a295-544751d1df83
-- statement:
--   Prove that in a finite abelian group $G$, there exists an element $g$ whose order divides the order of every element in $G$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76520 (G : Type*) [CommGroup G] [Finite G] : 
  ∃ g : G, ∀ h : G, orderOf g ∣ orderOf h   :=  by sorry
