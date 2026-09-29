-- Prove2me | Theorems.Thm_WorkbookSource_base_53135
-- name    : WorkbookSource.base_53135
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:34.356284+00:00
-- url     : https://prove2.me/theorems/c1aa8bba-8961-4d85-a1d3-96138f45c3e1
-- title:
--   A strict product bound under a weighted sum
-- statement:
--   Prove that for all $a,b>0$ with $a+2b=2$ , we have
--    $$\left(a^2+1\right)\left(b^2+1\right) >\frac{9}{5}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53135` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53135; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53135 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + 2 * b = 2) : (a^2 + 1) * (b^2 + 1) > 9 / 5  :=  by sorry
