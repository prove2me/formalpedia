-- Prove2me | Theorems.Thm_lean_workbook_plus_46671
-- name    : lean_workbook_plus_46671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e669370d-e600-45cc-9600-f20e39c11731
-- statement:
--   Solve for x and y in the system of equations: ${\begin{cases}x-y=p\\x+y=q\end{cases}}$ where $pq=240$ and $p\leqslant q$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46671 (p q x y : ℝ) (h₁ : x - y = p) (h₂ : x + y = q) (h₃ : p * q = 240) (h₄ : p ≤ q) : x = (q + p) / 2 ∧ y = (q - p) / 2   :=  by sorry
