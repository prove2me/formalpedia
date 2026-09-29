-- Prove2me | Theorems.Thm_lean_workbook_plus_44306
-- name    : lean_workbook_plus_44306
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5accb263-1953-4492-9d99-ca2f8934b1d1
-- statement:
--   Prove that $n^2$ divides $1^3 +3^3 +5^3 +...+(2n-1)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44306 : ∀ n, n^2 ∣ (∑ i in Finset.range n, (2 * i - 1)^3)   :=  by sorry
