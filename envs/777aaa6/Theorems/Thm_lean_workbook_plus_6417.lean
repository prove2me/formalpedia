-- Prove2me | Theorems.Thm_lean_workbook_plus_6417
-- name    : lean_workbook_plus_6417
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/58d53c32-b02e-4f2f-870f-cb7477bb4728
-- statement:
--   By AM-GM, we have \n\n $\frac{1^2+2^2+3^2+\cdots+n^2}{n} \ge \sqrt[n]{1^22^23^2\cdots n^2}$ , or \n\n $\frac{n(n+1)(2n+1)/6}{n}=\frac{(n+1)(2n+1)}{6} \ge \sqrt[n]{(n!)^2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6417 : ∀ n : ℕ, (∑ i in Finset.range n, i^2)/n ≥ (∏ i in Finset.range n, i^2)^(1/n)   :=  by sorry
