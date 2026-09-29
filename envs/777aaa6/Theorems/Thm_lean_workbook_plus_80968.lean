-- Prove2me | Theorems.Thm_lean_workbook_plus_80968
-- name    : lean_workbook_plus_80968
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a344c4b9-dd00-4801-8acf-6a02a8e5338e
-- statement:
--   Prove that for $n \geq 2$ and natural number, \(\frac{1}{(n+1)}(1+\frac{1}{3}+...+\frac{1}{2n-1}) > \frac{1}{n}(\frac{1}{2}+\frac{1}{4}+...+\frac{1}{2n})\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80968 : ∀ n ≥ 2, (1/(n+1)) * (∑ i in Finset.range n, 1/(2 * i + 2)) < (1/n) * (∑ i in Finset.range n, 1/(2 * i + 1))   :=  by sorry
