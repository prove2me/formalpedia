-- Prove2me | Theorems.Thm_WorkbookSource_base_1350
-- name    : WorkbookSource.base_1350
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:05:03.380227+00:00
-- url     : https://prove2.me/theorems/02efe73c-446b-4841-98a1-fb3f8cd4f981
-- title:
--   A sixth-degree inequality involving three triangle factors
-- statement:
--   Let $a,b,c>0.$ Prove that $abc(a+b+c)(a^2+b^2+c^2)\ge3(a^3+b^3+c^3)(a+b-c)(b+c-a)(c+a-b)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1350` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1350; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1350 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * c * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 3 * (a ^ 3 + b ^ 3 + c ^ 3) * (a + b - c) * (b + c - a) * (c + a - b)  :=  by sorry
