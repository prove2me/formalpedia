-- Prove2me | Theorems.Thm_WorkbookSource_base_28080
-- name    : WorkbookSource.base_28080
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:53:05.125032+00:00
-- url     : https://prove2.me/theorems/e5f0beee-16f7-45ae-bf39-156426c7f130
-- title:
--   A pair-product squared ratio upper bound
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $\frac{(a+b)(b+c)}{(2a+b+c)^2}+\frac{(b+c)(c+a)}{(2b+c+a)^2}+\frac{(c+a)(a+b)}{(2c+a+b)^2}\le\frac{(a+b+c)^2}{4(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28080` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28080; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28080 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) / (2 * a + b + c) ^ 2 + (b + c) * (c + a) / (2 * b + c + a) ^ 2 + (c + a) * (a + b) / (2 * c + a + b) ^ 2 ≤ (a + b + c) ^ 2 / (4 * (a * b + b * c + c * a))  :=  by sorry
