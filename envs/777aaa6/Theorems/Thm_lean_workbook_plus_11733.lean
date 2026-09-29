-- Prove2me | Theorems.Thm_lean_workbook_plus_11733
-- name    : lean_workbook_plus_11733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/44a7f16c-6f7e-4b8b-bca6-c8d634355c77
-- statement:
--   Beregner Fibonacci-følgeren $F_n$ ved å bruke rekursion: $F_1 = F_2 = 1$ og $F_{n+1} = F_n + F_{n-1}$. Finn $F_{8}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11733 (F : ℕ → ℕ) (h₁ : F 1 = 1 ∧ F 2 = 1) (h₂ : ∀ n, F (n + 2) = F (n + 1) + F n) : F 8 = 21   :=  by sorry
