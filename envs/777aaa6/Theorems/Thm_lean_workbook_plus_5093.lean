-- Prove2me | Theorems.Thm_lean_workbook_plus_5093
-- name    : lean_workbook_plus_5093
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4363b0fc-7dc9-42fa-9bec-3f4274bb7bec
-- statement:
--   Prove that $1*2+2*3+...+n*(n+1)=\frac{n(n+1)(n+2)}3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5093 (n : ℕ) : ∑ k in Finset.range (n+1), k * (k + 1) = n * (n + 1) * (n + 2) / 3   :=  by sorry
