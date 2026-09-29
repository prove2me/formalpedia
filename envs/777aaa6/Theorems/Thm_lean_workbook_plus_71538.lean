-- Prove2me | Theorems.Thm_lean_workbook_plus_71538
-- name    : lean_workbook_plus_71538
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/0848151a-12e6-4edf-b9a8-ac7c31b23e3a
-- statement:
--   Prove that $1*2+2*3+...+n*(n+1)=\frac{n(n+1)(n+2)}3$ using induction
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71538 : ∀ n, ∑ i in Finset.range (n+1), i * (i + 1) = n * (n + 1) * (n + 2) / 3   :=  by sorry
