-- Prove2me | Theorems.Thm_lean_workbook_plus_35629
-- name    : lean_workbook_plus_35629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9906894e-b213-4a3b-8002-d952c685aab0
-- statement:
--   number of dimes = x\nnumber of nickels = x-8\nnumber of quarters = 2x-16\nSince each one is worth different amounts\nwe find that $10x+5(x-8)+25(2x-16)=665$, expanding gives $65x-440 = 665$, $65x=1105$, $x=17$. Thus, Cah has 17 dimes.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35629  (x : ℕ)
  (h₀ : 10 * x + 5 * (x - 8) + 25 * (2 * x - 16) = 665) :
  x = 17   :=  by sorry
