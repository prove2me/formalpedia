-- Prove2me | Theorems.Thm_lean_workbook_plus_51240
-- name    : lean_workbook_plus_51240
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4490e78d-7714-4a69-a89c-e2e677c9d4c7
-- statement:
--   For which positive integers $n$ does $n$ divide $S(n)=1^{2011}+2^{2011}+....+(n-1)^{2011}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51240 (n : ℕ) (hn: n > 0) : n ∣ (∑ i in Finset.range n, i ^ 2011) ↔ n ∣ (∑ i in Finset.range n, i ^ 2011)   :=  by sorry
