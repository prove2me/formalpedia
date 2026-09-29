-- Prove2me | Theorems.Thm_lean_workbook_plus_71610
-- name    : lean_workbook_plus_71610
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b4f1ee28-a113-4a3d-8a58-27e12d9f785c
-- statement:
--   Find all functions $ f\colon \mathbb{Z} \to \mathbb{Z} $ such that \n\n $$ f(y) - f(y + f(x)) = x $$ for all $ x,y \in\mathbb{Z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71610 (f : ℤ → ℤ) (hf : ∀ x y, f y - f (y + f x) = x) : ∃ a, ∀ x, f x = a - x   :=  by sorry
