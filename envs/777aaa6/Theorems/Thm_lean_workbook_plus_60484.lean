-- Prove2me | Theorems.Thm_lean_workbook_plus_60484
-- name    : lean_workbook_plus_60484
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2a14e156-a08a-46a5-8fa0-9035c20c5eef
-- statement:
--   Take $A=\begin{pmatrix}1&0\\0&0\end{pmatrix},B=\begin{pmatrix}0&0\\0&1\end{pmatrix}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60484 (A B : Matrix (Fin 2) (Fin 2) ℚ) (hA : A =![![1, 0],![0, 0]]) (hB : B =![![0, 0],![0, 1]]) : A * B =![![0, 0],![0, 0]]   :=  by sorry
