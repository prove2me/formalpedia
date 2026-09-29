-- Prove2me | Theorems.Thm_lean_workbook_plus_21792
-- name    : lean_workbook_plus_21792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8f067b08-76dc-44da-aa3a-8af8a7882253
-- statement:
--   Beregner Fibonacci-følgeren $F_n$ ved å bruke rekursion: $F_1 = F_2 = 1$ og $F_{n+1} = F_n + F_{n-1}$. Finn $F_{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21792 (F : ℕ → ℕ) (h₁ : F 1 = 1) (h₂ : F 2 = 1) (h₃ : ∀ n, F (n + 2) = F (n + 1) + F n) : F 2 = 1   :=  by sorry
