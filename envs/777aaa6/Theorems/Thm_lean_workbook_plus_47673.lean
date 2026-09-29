-- Prove2me | Theorems.Thm_lean_workbook_plus_47673
-- name    : lean_workbook_plus_47673
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c58df90f-aba7-47e5-8354-e145194aac16
-- statement:
--   Prove that if $(a, b) = 1$ , where $(a, b)$ is the greatest common divisor of $a$ and $b$ , then $(a, b^{n}) = 1$ , for all $n \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47673 (a b : ℕ) (hab : Nat.Coprime a b) (n : ℕ) : Nat.Coprime a (b^n)   :=  by sorry
