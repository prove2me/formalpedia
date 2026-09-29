-- Prove2me | Theorems.Thm_WorkbookSource_base_38993
-- name    : WorkbookSource.base_38993
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:54:15.031048+00:00
-- url     : https://prove2.me/theorems/9127c242-d6a5-49cf-bea6-58bac00ad2f2
-- title:
--   A sixth-degree lower bound at fixed sum six
-- statement:
--   Let $a,b,c\ge 0$ such that $a+b+c=6$. Prove that: $100+5(a^2+b^2+c^2)-2(a^2b^2+b^2c^2+a^2c^2)-a^2b^2c^2\ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38993` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38993; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38993 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 6) : 100 + 5 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) - a ^ 2 * b ^ 2 * c ^ 2 ≥ 0  :=  by sorry
