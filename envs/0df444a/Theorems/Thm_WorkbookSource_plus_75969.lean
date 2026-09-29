-- Prove2me | Theorems.Thm_WorkbookSource_plus_75969
-- name    : WorkbookSource.plus_75969
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:58.47539+00:00
-- url     : https://prove2.me/theorems/667a54e5-0646-41b5-8ca3-18d0b5709693
-- title:
--   A shifted quadratic upper bound in three real variables
-- statement:
--   Let $a+b+c+\frac{1}{4} (a-c)^2+\frac{1}{2}(3-a^2-b^2-c^2 )\leqslant 3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75969` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75969; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75969 (a b c : ℝ) : a + b + c + (1 / 4) * (a - c) ^ 2 + (1 / 2) * (3 - a ^ 2 - b ^ 2 - c ^ 2) ≤ 3   :=  by sorry
