-- Prove2me | Theorems.Thm_lean_workbook_plus_80319
-- name    : lean_workbook_plus_80319
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/76e891ad-c075-4dd2-849e-26ab42bb88a9
-- statement:
--   Claim: for every positive integer $n$ ,the following equation holds: $\sum_{d|n}\varphi(d)=n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80319 : ∀ n, n > 0 → ∑ d in n.divisors, φ d = n   :=  by sorry
