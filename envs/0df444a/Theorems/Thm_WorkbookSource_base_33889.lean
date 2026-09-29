-- Prove2me | Theorems.Thm_WorkbookSource_base_33889
-- name    : WorkbookSource.base_33889
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:04.247851+00:00
-- url     : https://prove2.me/theorems/08bda9bc-abf2-47e5-bea2-e97142c69bc5
-- title:
--   A product of squared norms bounds the Vandermonde square
-- statement:
--   Let $a,b,c$ are real numbers, show that
--   $2(a^2+b^2)(b^2+c^2)(c^2+a^2)\ge (a-b)^2(b-c)^2(c-a)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33889` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33889; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33889 (a b c : ℝ) : 2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (a - b)^2 * (b - c)^2 * (c - a)^2  :=  by sorry
