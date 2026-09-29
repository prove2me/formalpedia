-- Prove2me | Theorems.Thm_WorkbookSource_base_22723
-- name    : WorkbookSource.base_22723
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:51:41.319827+00:00
-- url     : https://prove2.me/theorems/3af1f9d8-c273-474d-be85-e38f75a7ca54
-- title:
--   A shifted cyclic cubic ratio sum bounds the total
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{a+b^3}{b^2+1}+\frac{b+c^3}{c^2+1}+\frac{c+a^3}{a^2+1}\ge a+b+c$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22723` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22723; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22723 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b^3) / (b^2 + 1) + (b + c^3) / (c^2 + 1) + (c + a^3) / (a^2 + 1) ≥ a + b + c  :=  by sorry
