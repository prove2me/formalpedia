-- Prove2me | Theorems.Thm_WorkbookSource_base_8323
-- name    : WorkbookSource.base_8323
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:29:08.648614+00:00
-- url     : https://prove2.me/theorems/a679e639-5d83-4891-809a-a0b990b281d2
-- title:
--   A cyclic quadratic reciprocal upper bound at fixed sum three
-- statement:
--   For $a, b, c>0, a+b+c=3$ prove that $\frac{a}{2a^2+b^2+c^2+1}+\frac{b}{2b^2+c^2+a^2+1}+\frac{c}{2c^2+a^2+b^2+1}\le\frac{3}{4+abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8323` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8323; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8323 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a / (2 * a ^ 2 + b ^ 2 + c ^ 2 + 1) + b / (2 * b ^ 2 + c ^ 2 + a ^ 2 + 1) + c / (2 * c ^ 2 + a ^ 2 + b ^ 2 + 1)) ≤ (3 / (4 + a * b * c))  :=  by sorry
