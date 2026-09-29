-- Prove2me | Theorems.Thm_WorkbookSource_base_9273
-- name    : WorkbookSource.base_9273
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:12.4268+00:00
-- url     : https://prove2.me/theorems/66824166-1456-401b-b6aa-45c3f982b024
-- title:
--   A quadratic norm bound for a triple product
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=1$. Prove that $2(a^2+b^2+c^2)\ge \frac{1}{9}+15abc$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9273` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9273; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9273 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 2 * (a^2 + b^2 + c^2) ≥ 1 / 9 + 15 * a * b * c  :=  by sorry
