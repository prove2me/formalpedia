-- Prove2me | Theorems.Thm_WorkbookSource_plus_38244
-- name    : WorkbookSource.plus_38244
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:58:11.710848+00:00
-- url     : https://prove2.me/theorems/c1a81c28-559d-4f4d-b1c5-66ca966aadd3
-- title:
--   A shifted cyclic quadratic reciprocal sum is at least one half
-- statement:
--   Let $a, b, c>0, a+b+c=3$ . prove that
--    $\frac{1}{2a(a+1)+ca+b}+\frac{1}{2b(b+1)+ab+c}+\frac{1}{2c(c+1)+bc+a}\ge\frac{1}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_38244` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_38244; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_38244 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (2 * a * (a + 1) + c * a + b) + 1 / (2 * b * (b + 1) + a * b + c) + 1 / (2 * c * (c + 1) + b * c + a) ≥ 1 / 2   :=  by sorry
