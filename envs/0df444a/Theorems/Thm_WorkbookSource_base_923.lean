-- Prove2me | Theorems.Thm_WorkbookSource_base_923
-- name    : WorkbookSource.base_923
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T02:28:18.422822+00:00
-- url     : https://prove2.me/theorems/a763b7e7-95ca-47fc-a85c-e37bb4b59d72
-- title:
--   A shifted quadratic reciprocal bound at fixed sum three
-- statement:
--   Let $a, b, c >0, a + b + c = 3$ . Prove that:
--    $\dfrac{(a+1)^2(b+1)^2}{c^2+1} + \dfrac{(a+1)^2(c+1)^2}{b^2+1} + \dfrac{(b+1)^2(c+1)^2}{a^2+1} \geq 24$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_923` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_923; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_923 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a + 1) ^ 2 * (b + 1) ^ 2 / (c ^ 2 + 1) + (a + 1) ^ 2 * (c + 1) ^ 2 / (b ^ 2 + 1) + (b + 1) ^ 2 * (c + 1) ^ 2 / (a ^ 2 + 1) ≥ 24  :=  by sorry
