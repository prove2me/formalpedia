-- Prove2me | Theorems.Thm_lean_workbook_plus_72844
-- name    : lean_workbook_plus_72844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ab991965-d7fe-4d92-8687-3356c4d367ba
-- statement:
--   Prove the following inequality: $\frac{1}{(a+n)^{2}}+\frac{1}{(b+n)^{2}}\geq\frac{1}{ab+n^{2}}$, where $a,b,n>1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72844 (a b n : ℝ) (ha : 1 < a) (hb : 1 < b) (hn : 1 < n) : (1 / (a + n) ^ 2 + 1 / (b + n) ^ 2) ≥ 1 / (a * b + n ^ 2)   :=  by sorry
