-- Prove2me | Theorems.Thm_lean_workbook_plus_75396
-- name    : lean_workbook_plus_75396
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/863218dc-2895-4bc1-9f8f-abd82444a6b1
-- statement:
--   Let $ A \in \mathcal{M}_2 \left(\mathbb{Q}\right)$ , such that $ \det(A^2-2I_2)=0$ . Prove that $ A^2=2I_2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75396 {A : Matrix (Fin 2) (Fin 2) ℚ} (hA : A ^ 2 - 2 • (1 : Matrix (Fin 2) (Fin 2) ℚ) = 0) : A ^ 2 = 2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)   :=  by sorry
