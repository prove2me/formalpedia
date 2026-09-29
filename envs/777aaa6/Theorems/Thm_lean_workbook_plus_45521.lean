-- Prove2me | Theorems.Thm_lean_workbook_plus_45521
-- name    : lean_workbook_plus_45521
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/f93eca4f-6286-4930-8311-cabbc604c789
-- statement:
--   Find all triplets of integers $(x,y,z)$ such that $xy(x^2-y^2)+yz(y^2-z^2)+zx(z^2-x^2)=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45521 (x y z : ℤ) (h : x * y * (x ^ 2 - y ^ 2) + y * z * (y ^ 2 - z ^ 2) + z * x * (z ^ 2 - x ^ 2) = 1) : (x = 0 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = -1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = -1 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = -1 ∧ z = 0) ∨ (x = -1 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 0 ∧ z = -1) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = -1 ∧ y = 0 ∧ z = -1) ∨ (x = 0 ∧ y = 1 ∧ z = 1) ∨ (x = 0 ∧ y = -1 ∧ z = -1)   :=  by sorry
