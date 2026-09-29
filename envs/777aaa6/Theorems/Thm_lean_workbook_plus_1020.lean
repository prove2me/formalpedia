-- Prove2me | Theorems.Thm_lean_workbook_plus_1020
-- name    : lean_workbook_plus_1020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/69581f3d-a266-4b7e-bb35-c8b56a950b29
-- statement:
--   X Mod Y is $\equiv$ to Z Mod Y if The remainder when X is divided by Y is the same as the remainder when Z is divided by Y
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1020 (X Y Z : ℕ) (h₁ : X % Y = Z % Y) : X ≡ Z [MOD Y]   :=  by sorry
