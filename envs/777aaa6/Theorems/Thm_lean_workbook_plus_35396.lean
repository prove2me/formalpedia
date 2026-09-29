-- Prove2me | Theorems.Thm_lean_workbook_plus_35396
-- name    : lean_workbook_plus_35396
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/be486a91-2892-4b8a-af6a-5a8ea211c050
-- statement:
--   Let $n=2k$ so that $n^4+n^3+n^2+n+1=16k^4+40k^3+40k^2+20k+5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35396  (n : ℕ)
  (k : ℕ)
  (h₀ : n = 2 * k) :
  n^4 + n^3 + n^2 + n + 1 = 16 * k^4 + 40 * k^3 + 40 * k^2 + 20 * k + 5   :=  by sorry
