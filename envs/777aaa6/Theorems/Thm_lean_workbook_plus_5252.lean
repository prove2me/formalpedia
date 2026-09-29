-- Prove2me | Theorems.Thm_lean_workbook_plus_5252
-- name    : lean_workbook_plus_5252
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7d7b9a39-a1c4-450f-b837-957220ce860f
-- statement:
--   Let matrices $A,B\in M_n(\mathbb R)$ such that $AB=BA$ , the matrix $A-B$ is nilpotent. Prove that $det(A)=det(B)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5252 {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : A * B = B * A) (hA : A - B = 0) : A.det = B.det   :=  by sorry
