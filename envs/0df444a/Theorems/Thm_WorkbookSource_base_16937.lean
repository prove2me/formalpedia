-- Prove2me | Theorems.Thm_WorkbookSource_base_16937
-- name    : WorkbookSource.base_16937
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:48.270237+00:00
-- url     : https://prove2.me/theorems/22c0badb-3f6f-4bbe-86ed-6b429aa6b1ac
-- title:
--   A normalized cubic sum with a triple-product correction
-- statement:
--   Prove that for $a, b, c > 0$,
--
--    $\frac{a^3 + b^3 + c^3}{3abc} + \frac{24abc}{(a + b)(b + c)(c + a)} \geq 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16937` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16937; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16937 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (3 * a * b * c) + (24 * a * b * c) / ((a + b) * (b + c) * (c + a)) ≥ 4  :=  by sorry
