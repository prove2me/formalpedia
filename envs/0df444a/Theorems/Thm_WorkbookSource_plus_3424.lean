-- Prove2me | Theorems.Thm_WorkbookSource_plus_3424
-- name    : WorkbookSource.plus_3424
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:57:09.710725+00:00
-- url     : https://prove2.me/theorems/86c018ca-648c-492a-811f-0007c981c93f
-- title:
--   A mixed cyclic quadratic ratio upper bound at fixed sum three
-- statement:
--   Let $a, b, c>0, a+b+c=3$ . prove that
--    $M$ = $\frac{a^2}{2a(a+1)+ca+b}+\frac{b^2}{2b(b+1)+ab+c}+\frac{c^2}{2c(c+1)+bc+a}\le\frac{1}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_3424` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_3424; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_3424 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / (2 * a * (a + 1) + c * a + b) + b^2 / (2 * b * (b + 1) + a * b + c) + c^2 / (2 * c * (c + 1) + b * c + a) ≤ 1 / 2   :=  by sorry
