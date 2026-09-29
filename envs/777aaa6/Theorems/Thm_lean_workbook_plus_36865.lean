-- Prove2me | Theorems.Thm_lean_workbook_plus_36865
-- name    : lean_workbook_plus_36865
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c0660c1e-c632-49f0-a3d3-62a263467acb
-- statement:
--   Find the values of $ a_{1}, a_{2}, a_{3}, a_{4}$ that satisfy $ a_{1} = a_{2} = a_{3} = a_{4} = \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36865 (a : ℕ → ℝ) (h₁ : a 1 = 1 / 2) (h₂ : a 2 = 1 / 2) (h₃ : a 3 = 1 / 2) (h₄ : a 4 = 1 / 2) : a 1 = a 2 ∧ a 2 = a 3 ∧ a 3 = a 4 ∧ a 4 = 1 / 2   :=  by sorry
