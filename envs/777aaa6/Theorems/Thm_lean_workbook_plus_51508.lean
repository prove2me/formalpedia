-- Prove2me | Theorems.Thm_lean_workbook_plus_51508
-- name    : lean_workbook_plus_51508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6402dda8-68e0-41a5-9c6c-eebba3ca7405
-- statement:
--   Let $A,B \in M(n,C)$ be matrices such that $AB=A$ and $BA=B$. Prove that $(A-B)^2=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51508 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = A) (hBA : B * A = B) : (A - B) ^ 2 = 0   :=  by sorry
