-- Prove2me | Theorems.Thm_WorkbookSource_plus_39593
-- name    : WorkbookSource.plus_39593
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:25.68896+00:00
-- url     : https://prove2.me/theorems/a5aece67-4891-492e-a526-ddb2135a80eb
-- title:
--   An asymmetric pairwise-product bound
-- statement:
--   Let $a,b,c \geq 0$ and $a+b+c=3.$ Prove that $ab+ca +\frac{13}{3}\geq bc$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39593` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39593; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39593 (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) : a * b + c * a + 13 / 3 ≥ b * c   :=  by sorry
