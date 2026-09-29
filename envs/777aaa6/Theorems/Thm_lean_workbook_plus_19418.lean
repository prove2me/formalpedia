-- Prove2me | Theorems.Thm_lean_workbook_plus_19418
-- name    : lean_workbook_plus_19418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/602293ea-30dd-402f-a986-be88153fb756
-- statement:
--   Derive the recursive relation $f(x+1) = cf(x) - f(x-1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19418 (f : ℤ → ℤ) (c : ℤ) (h : ∀ x, f (x + 1) = c * f x - f (x - 1)) : ∀ x, f (x + 1) = c * f x - f (x - 1)   :=  by sorry
