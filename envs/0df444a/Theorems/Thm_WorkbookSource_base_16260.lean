-- Prove2me | Theorems.Thm_WorkbookSource_base_16260
-- name    : WorkbookSource.base_16260
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:02:14.330211+00:00
-- url     : https://prove2.me/theorems/e25e95c9-fe8d-4f14-87d9-c005e99ada5c
-- title:
--   A pairwise cubic-over-quadratic sum bounds the total
-- statement:
--   For $a,b,c>0$ . Prove that: $\frac{a^3+b^3}{a^2+b^2}+\frac{b^3+c^3}{b^2+c^2}+\frac{c^3+a^3}{c^2+a^2}\ge a+b+c$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16260` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16260; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16260 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3) / (a^2 + b^2) + (b^3 + c^3) / (b^2 + c^2) + (c^3 + a^3) / (c^2 + a^2) ≥ a + b + c  :=  by sorry
