-- Prove2me | Theorems.Thm_lean_workbook_plus_62795
-- name    : lean_workbook_plus_62795
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6d129c5e-3121-4e90-bb33-14d6913afff8
-- statement:
--   Let $ f$ be a function such that for all integers $ x$ and $ y$ applies $ f(x+y) = f(x) + f(y) + 6xy + 1$ and $ f(x) = f(-x)$ . Then $ f(3)$ equals
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62795 (f : ℤ → ℤ) (hf1 : ∀ x y, f (x + y) = f x + f y + 6 * x * y + 1) (hf2 : ∀ x, f x = f (-x)) : f 3 = 26   :=  by sorry
