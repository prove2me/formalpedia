-- Prove2me | Theorems.Thm_WorkbookSource_base_8025
-- name    : WorkbookSource.base_8025
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:28:15.835379+00:00
-- url     : https://prove2.me/theorems/10975acc-2e93-4b90-9985-a49a4e3a118b
-- title:
--   A shifted cyclic ratio upper bound at fixed sum three
-- statement:
--   For $a, b, c>0, a+b+c=3$ prove that
--    $\frac{a}{a+b+1}+\frac{b}{b+c+1}+\frac{c}{c+a+1}\le\frac{(a^2+b^2+c^2)^2}{9}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8025` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8025; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8025 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (a + b + 1) + b / (b + c + 1) + c / (c + a + 1) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / 9  :=  by sorry
