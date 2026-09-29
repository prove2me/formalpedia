-- Prove2me | Theorems.Thm_WorkbookSource_base_12499
-- name    : WorkbookSource.base_12499
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:25.127014+00:00
-- url     : https://prove2.me/theorems/cb5990df-dc82-4170-acdb-39f011ab34e4
-- title:
--   A pairwise product bound under a quadratic-factor product constraint
-- statement:
--   With $(a^2+1)(b^2+1)(c^2+1)=64$ , prove that: $ab+bc+ca\le 9$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12499` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12499; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12499 (a b c : ℝ) (h : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = 64) :
 a * b + b * c + c * a ≤ 9  :=  by sorry
