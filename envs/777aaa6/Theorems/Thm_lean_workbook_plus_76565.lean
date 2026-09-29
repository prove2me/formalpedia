-- Prove2me | Theorems.Thm_lean_workbook_plus_76565
-- name    : lean_workbook_plus_76565
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/691c10cb-44ba-4510-a3d9-81585dce068d
-- statement:
--   Note that \n\n \begin{align*} f_4(x) &= \sin^4{x}+\cos^4{x} \ &= (\sin^2{x} + \cos^2{x})^2 - 2\sin^2{x}\cos^2{x} \ &= 1 - 2\sin^2{x}\cos^2{x}, \end{align*} \n\nand \n\n \begin{align*} f_6(x) &= \sin^6{x}+\cos^6{x} \ &= (\sin^2{x}+\cos^2{x})(\sin^4{x}-\sin^2{x}\cos^2{x}+\cos^4{x}) \ &= 1 - 3\sin^2{x}\cos^2{x}. \end{align*} \n\nHence, we have \n\n \begin{align*} 6f_4(x)-4f_6(x) &= 6 - 12\sin^2{x}\cos^2{x} - 4 + 12\sin^2{x}\cos^2{x} \ &= 2 \ &= 2f_2(x). \end{align*} \n\nSo, it holds for all $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76565  (x : ℝ) :
  6 * (Real.sin x ^ 4 + Real.cos x ^ 4) - 4 * (Real.sin x ^ 6 + Real.cos x ^ 6) = 2 * (Real.sin x ^ 2 + Real.cos x ^ 2)   :=  by sorry
