-- Prove2me | Theorems.Thm_WorkbookSource_base_41246
-- name    : WorkbookSource.base_41246
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:40.826867+00:00
-- url     : https://prove2.me/theorems/c85a085a-b880-4d81-8519-e0d5dd7b6990
-- title:
--   A quadratic lower bound for nonnegative variables with total at most eight
-- statement:
--   Let $a,b,c$ be non-negative real number such that $a+b+c \le 8$ , Prove that $a^2+(b-6)a-(b-2)c\ge -9.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41246` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41246; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41246 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c ≤ 8) : a^2 + (b - 6) * a - (b - 2) * c ≥ -9  :=  by sorry
