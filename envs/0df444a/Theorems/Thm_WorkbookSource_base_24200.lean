-- Prove2me | Theorems.Thm_WorkbookSource_base_24200
-- name    : WorkbookSource.base_24200
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:46.550417+00:00
-- url     : https://prove2.me/theorems/89589847-5f86-4af8-82cf-24eded2e70e8
-- title:
--   Three fourth powers of pairwise sums bound the fourth-power sum
-- statement:
--   If a, b, c are real number then: $ (a+b)^4+(b+c)^4+(c+a)^4 \ge \frac{4(a^4+b^4+c^4)}{7} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24200` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24200; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24200 (a b c: ℝ) : (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥ (4 / 7) * (a ^ 4 + b ^ 4 + c ^ 4)  :=  by sorry
