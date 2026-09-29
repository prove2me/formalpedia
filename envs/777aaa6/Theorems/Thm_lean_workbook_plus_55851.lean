-- Prove2me | Theorems.Thm_lean_workbook_plus_55851
-- name    : lean_workbook_plus_55851
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/0534a91a-1b74-41ea-9f08-edb538b22575
-- statement:
--   $\implies$ $\frac{t(t+1)}{2}+\frac{(k-t)(t+3k+1)}2=2021$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55851 ∀ t k : ℕ, ((t * (t + 1)) / 2 + ((k - t) * (t + 3 * k + 1)) / 2 = 2021 ↔ (k = 13 ∧ t = 7)) ∨ (k = 10 ∧ t = 20)   :=  by sorry
