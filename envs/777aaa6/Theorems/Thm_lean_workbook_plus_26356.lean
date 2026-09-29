-- Prove2me | Theorems.Thm_lean_workbook_plus_26356
-- name    : lean_workbook_plus_26356
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ad8bf8e5-f202-4713-954b-97713ba09820
-- statement:
--   If $ f(x)=x^2+x+1$ then $ f(-1)+f(0)+f(1)$ is equal with: \n\n $ (A)$ $ 1$ \n $ (B)$ $ 2$ \n $ (C)$ $ 3$ \n $ (D)$ $ 4$ \n $ (E)$ $ 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26356 (f : ℤ → ℤ) (f_def : ∀ x, f x = x^2 + x + 1) : f (-1) + f 0 + f 1 = 5   :=  by sorry
