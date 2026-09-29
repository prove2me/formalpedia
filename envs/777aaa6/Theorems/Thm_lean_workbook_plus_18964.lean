-- Prove2me | Theorems.Thm_lean_workbook_plus_18964
-- name    : lean_workbook_plus_18964
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/253d0113-f399-4822-9e42-d27bc78ba482
-- statement:
--   Find, with proof, all functions $f$ mapping integers to integers with the property that for all integers $m,n$ , $f(m)+f(n)= \max\left(f(m+n),f(m-n)\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18964 (f : ℤ → ℤ) (hf: f m + f n = max (f (m + n)) (f (m - n))) : ∃ A : Set ℤ, ∀ x : ℤ, x ∈ A ↔ ∃ a : ℤ, ∀ y : ℤ, y ∈ A ↔ y = a * x   :=  by sorry
