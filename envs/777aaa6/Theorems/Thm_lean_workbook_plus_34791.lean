-- Prove2me | Theorems.Thm_lean_workbook_plus_34791
-- name    : lean_workbook_plus_34791
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/06b4cc62-2d49-4994-8f85-5df6f3dee29e
-- statement:
--   Find the solutions of the following equations in $\mathbb{Z}_{6}$ residue class mod 6: \n1) 5 ⊗ x ⊕ 2 = 4 \n2) 3 ⊗ x ⊕ 4 = 4 \n3) 2 ⊗ x ⊕ 3 = 2 \n\nwhere the symbols are: ⊕ for addition and ⊗ for multiplication mod 6.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34791 (x : ℕ) (h₁ : (5 * x + 2) % 6 = 4) (h₂ : (3 * x + 4) % 6 = 4) (h₃ : (2 * x + 3) % 6 = 2) : x ≡ 1 [ZMOD 6] ∨ x ≡ 3 [ZMOD 6] ∨ x ≡ 5 [ZMOD 6]   :=  by sorry
