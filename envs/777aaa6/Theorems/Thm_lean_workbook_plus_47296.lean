-- Prove2me | Theorems.Thm_lean_workbook_plus_47296
-- name    : lean_workbook_plus_47296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/fd0c2697-2f89-4924-a2be-2abc495c5127
-- statement:
--   Beregner Fibonacci-følgeren $F_n$ ved å bruke rekursion: $F_1 = F_2 = 1$ og $F_{n+1} = F_n + F_{n-1}$. Finn $F_{5}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47296 (F : ℕ → ℕ) (h₁ : F 1 = 1) (h₂ : F 2 = 1) (h₃ : ∀ n, F (n + 2) = F (n + 1) + F n) : F 5 = 5   :=  by sorry
