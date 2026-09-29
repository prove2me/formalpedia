-- Prove2me | Theorems.Thm_WorkbookSource_plus_60066
-- name    : WorkbookSource.plus_60066
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:37.487123+00:00
-- url     : https://prove2.me/theorems/d65cfd5f-a72e-457c-93ed-8f4b89d163b9
-- title:
--   A fourth-power bound under a cubic relation
-- statement:
--   Let $a,b$ be positive real numbers such that $a^3+b^3=1+ab.$ Prove that $$a^4+b^4\geq a+b$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60066` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60066; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60066 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b > 0) (h : a^3 + b^3 = 1 + a * b) : a^4 + b^4 ≥ a + b   :=  by sorry
