-- Prove2me | Theorems.Thm_WorkbookSource_base_54998
-- name    : WorkbookSource.base_54998
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:13.944822+00:00
-- url     : https://prove2.me/theorems/6211629d-7c5d-4dae-9e89-7d8facb743d8
-- title:
--   A quadratic lower bound with mixed and linear terms
-- statement:
--   Prove that for any real numbers $a,b$ : $12 a^2+36 a b+36 b^2+7 \geq 18 a+24 b.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54998` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54998; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54998 (a b : ℝ) : 12 * a ^ 2 + 36 * a * b + 36 * b ^ 2 + 7 ≥ 18 * a + 24 * b  :=  by sorry
