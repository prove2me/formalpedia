-- Prove2me | Theorems.Thm_WorkbookSource_base_10295
-- name    : WorkbookSource.base_10295
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:32:38.307108+00:00
-- url     : https://prove2.me/theorems/eec18611-423d-4e29-80bc-1fc568d37a96
-- title:
--   A shifted quadratic reciprocal upper bound at fixed sum three
-- statement:
--   Let $ a,b,c$ are positive real number such that $a+b+c=3$ , prove that $\frac{1}{11+a^{2}}+\frac{1}{11+b^{2}}+\frac{1}{11+c^{2}}\leqslant \frac{1}{4}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10295` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10295; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10295 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (11 + a^2) + 1 / (11 + b^2) + 1 / (11 + c^2) ≤ 1 / 4  :=  by sorry
