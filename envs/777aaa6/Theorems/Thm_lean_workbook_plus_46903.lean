-- Prove2me | Theorems.Thm_lean_workbook_plus_46903
-- name    : lean_workbook_plus_46903
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/2c52f5d6-beed-4ee4-af15-5d6e2d21fb9f
-- statement:
--   Let $p_{A} (\lambda)$ denote the characteristic polynomial of $A$ . If \n\n $$p_{A} (\lambda) = \lambda^{3} - 17 \lambda^{2} + 2023 \lambda - 315$$ \nfor a $3 \times 3$ matrix $A$ , find the values of $\det(A)$ , $\operatorname{tr}(A)$ , $\operatorname{tr}(A^{2})$ , and $\operatorname{tr}(A^{3})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46903 (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.charpoly = X^3 - 17*X^2 + 2023*X - 315) : A.det = -315 ∧ A.trace = 17 ∧ A.trace^2 = 2023 ∧ A.trace^3 = -315   :=  by sorry
