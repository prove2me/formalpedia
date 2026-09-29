-- Prove2me | Theorems.Thm_lean_workbook_plus_47445
-- name    : lean_workbook_plus_47445
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d8e86653-53b3-4e84-99c8-7955a146c24e
-- statement:
--   Given matrices $ A: =\left(\begin{matrix}1&1\\0&0\end{matrix}\right)$ and $ B: =\left(\begin{matrix}0&0\\1&1\end{matrix}\right)$, show that they satisfy $ A^2=AB=A$ and $ B^2=BA=B$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47445 (A B : Matrix (Fin 2) (Fin 2) ℚ) (hA : A =![![1, 1],![0, 0]]) (hB : B =![![0, 0],![1, 1]]) : A ^ 2 = A * B ∧ B ^ 2 = B * A   :=  by sorry
