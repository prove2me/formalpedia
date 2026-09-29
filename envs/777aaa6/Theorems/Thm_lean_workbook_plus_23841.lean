-- Prove2me | Theorems.Thm_lean_workbook_plus_23841
-- name    : lean_workbook_plus_23841
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3ccdafc9-4e69-4b97-9f07-e05b7f21b645
-- statement:
--   Let $ A_i=b_i+c_i$ , $ B_i=a_i+c_i$ , $ C_i=a_i+b_i$ and $ s_i=a_i+b_i+c_i$ . It is easy to see that $ a_i^2+b_i^2+c_i^2+s_i^2=A_i^2+B_i^2+C_i^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23841 (a b c s A B C : ℕ → ℕ) (hA : A = b + c) (hB : B = a + c) (hC : C = a + b) (hs : s = a + b + c) : a^2 + b^2 + c^2 + s^2 = A^2 + B^2 + C^2   :=  by sorry
