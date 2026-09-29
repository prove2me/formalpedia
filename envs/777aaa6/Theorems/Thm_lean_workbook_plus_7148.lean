-- Prove2me | Theorems.Thm_lean_workbook_plus_7148
-- name    : lean_workbook_plus_7148
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/296f416b-b0c5-40bb-975f-bb75f7b0a43f
-- statement:
--   In the second case $wxyz=2^11*3^5$ , and $w$ , $x$ , $y$ and $z$ are in $\{24,27,32\}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7148 : ∃ w x y z : ℕ, w ∈ ({24, 27, 32} : Finset ℕ) ∧ x ∈ ({24, 27, 32} : Finset ℕ) ∧ y ∈ ({24, 27, 32} : Finset ℕ) ∧ z ∈ ({24, 27, 32} : Finset ℕ) ∧ w*x*y*z = 2^11*3^5   :=  by sorry
