-- Prove2me | Theorems.Thm_WorkbookSource_base_4034
-- name    : WorkbookSource.base_4034
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:01:08.101961+00:00
-- url     : https://prove2.me/theorems/0a54ddbe-83ed-4010-8002-594fb3f38957
-- title:
--   A sharp bound for pairwise squares and a triple product
-- statement:
--   Given: $a,b,c\geq 0$ and $a+b+c=2$ .
--   Prove that: $a^2b^2+b^2c^2+c^2a^2+abc\leq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4034` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4034; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4034 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 2) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c ≤ 1  :=  by sorry
