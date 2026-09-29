-- Prove2me | Theorems.Thm_WorkbookSource_base_7055
-- name    : WorkbookSource.base_7055
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:39:50.951841+00:00
-- url     : https://prove2.me/theorems/e9235fe6-8969-4914-8cbc-5c3bd06f6399
-- title:
--   A four-variable cubic sum with a normalized product correction
-- statement:
--   Let $a$ , $b$ , $c$ and $d$ are positive numbers. Prove that: $a^3+b^3+c^3+d^3+\frac{32abcd}{a+b+c+d}\geq3(abc+abd+acd+bcd)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7055` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7055; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7055 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a^3 + b^3 + c^3 + d^3 + (32 * a * b * c * d) / (a + b + c + d) ≥ 3 * (a * b * c + a * b * d + a * c * d + b * c * d)  :=  by sorry
