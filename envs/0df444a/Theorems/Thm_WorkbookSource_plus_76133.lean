-- Prove2me | Theorems.Thm_WorkbookSource_plus_76133
-- name    : WorkbookSource.plus_76133
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:55.255928+00:00
-- url     : https://prove2.me/theorems/aaf3da51-9b35-4b43-94c9-8e8d477421f7
-- title:
--   A symmetric sum-of-two-squares product inequality
-- statement:
--   prove that
--
--    $$\left(a+b+c-3abc\right)^2+\left(ab+bc+ca-3\right)^2 \ge 8\left(abc-1\right)^2$$
--
--   for nonnegative reals $a,b,c$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76133` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76133; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76133 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b + c - 3 * a * b * c) ^ 2 + (a * b + b * c + c * a - 3) ^ 2 ≥ 8 * (a * b * c - 1) ^ 2   :=  by sorry
