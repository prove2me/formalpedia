-- Prove2me | Theorems.Thm_lean_workbook_plus_38120
-- name    : lean_workbook_plus_38120
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d337d2a4-61ac-4adb-b872-831c4de6cc19
-- statement:
--   Yes (and it's true over any field): \n\n $\begin{pmatrix}I&0\\B&I\end{pmatrix} \begin{pmatrix}AB-I&A\\0&-I\end{pmatrix} \begin{pmatrix}I&0\\-B&I\end{pmatrix} = \begin{pmatrix}-I&A\\0&BA-I\end{pmatrix}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38120 (R : Type*) [Field R] (A B : Matrix (Fin 2) (Fin 2) R) : 
 !![1, 0; B, 1] *!![A * B - 1, A; 0, -1] *!![1, 0; -B, 1] =!![-1, A; 0, B * A - 1]   :=  by sorry
