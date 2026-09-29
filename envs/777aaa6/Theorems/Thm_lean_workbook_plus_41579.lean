-- Prove2me | Theorems.Thm_lean_workbook_plus_41579
-- name    : lean_workbook_plus_41579
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7568558b-d8d9-462d-a259-69eee4d46421
-- statement:
--   The well-known inequalities \n $\left(\\frac{k}{k-1}\\right)^{k-1}=\\left(1+\\frac1{k-1}\\right)^{k-1}<e<\\left(1+\\frac1k\\right)^{k+1}=\\left(\\frac{k+1}{k}\\right)^{k+1}$ \n hold for all integers $k\\ge 2$ . Multiplying these inequalities for $k=2,3,4,\\ldots,n$ yields \n \n \begin{align*} \n \\left(\\frac 21\\right)^1\\left(\\frac 32\\right)^2\\left(\\frac43\\right)^3\\cdots\\left(\\frac{n}{n-1}\\right)^{n-1} \n &<e^{n-1}< \n \\left(\\frac32\\right)^3\\left(\\frac43\\right)^4\\left(\\frac54\\right)^5\\cdots\\left(\\frac{n+1}{n}\\right)^{n+1} \n \n \\frac{2^1\\cdot 3^2\\cdot 4^3\\cdots n^{n-1}}{1^1\\cdot 2^2\\cdot 3^3\\cdots (n-1)^{n-1}} &< e^{n-1} < \n \\frac{3^3\\cdot 4^4\\cdot 5^5\\cdots (n+1)^{n+1}}{2^3\\cdot 3^4\\cdot 4^5\\cdots n^{n+1}} \n \n \\frac{n^{n-1}}{(n-1)!} &<e^{n-1} < \n \\frac{(n+1)^{n+1}}{4\\cdot n!} \n \n \\frac{n^n}{n!} &<e^{n-1} < \n \\frac{(n+1)^{n+1}}{4\\cdot n!}. \n \end{align*} \n Multiplying through by $e^{-n+1}n!$ gives the desired inequalities.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41579 : ∀ n : ℕ, (n : ℝ)^n / n! < e^(n-1) ∧ e^(n-1) < (n+1)^(n+1) / (4 * n!)   :=  by sorry
