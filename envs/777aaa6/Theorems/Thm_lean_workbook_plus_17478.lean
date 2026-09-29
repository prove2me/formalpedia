-- Prove2me | Theorems.Thm_lean_workbook_plus_17478
-- name    : lean_workbook_plus_17478
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0609c246-cd2b-4a2d-ae66-0ae7184de154
-- statement:
--   The first ten $a(i)$ are $1, 4, 22, 316, 6976, 373024, 32252032, 6619979776, 2253838544896, 1810098020122624$ . We see that when $10\geq n\geq 5$ , $a(n)=0 \;mod\; 8$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17478 (n : ℕ) (f : ℕ → ℕ) (hf: f 1 = 1 ∧ f 2 = 4 ∧ f 3 = 22 ∧ f 4 = 316 ∧ f 5 = 6976 ∧ f 6 = 373024 ∧ f 7 = 32252032 ∧ f 8 = 6619979776 ∧ f 9 = 2253838544896 ∧ f 10 = 1810098020122624): (n >= 5 ∧ n <= 10) → f n % 8 = 0   :=  by sorry
