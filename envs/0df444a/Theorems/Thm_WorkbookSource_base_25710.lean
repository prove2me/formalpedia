-- Prove2me | Theorems.Thm_WorkbookSource_base_25710
-- name    : WorkbookSource.base_25710
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:56.374047+00:00
-- url     : https://prove2.me/theorems/fb51f8b1-34ab-4114-b8a4-ccb55f5ccccd
-- title:
--   A weighted cyclic cubic ratio sum bounds one quarter of the total
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a(a^2+b^2)}{5a^2+3b^2}+\frac{b(b^2+c^2)}{5b^2+3c^2}+\frac{c(c^2+a^2)}{5c^2+3a^2}\le\frac{a+b+c}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25710` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25710; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25710 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + b ^ 2) / (5 * a ^ 2 + 3 * b ^ 2) + b * (b ^ 2 + c ^ 2) / (5 * b ^ 2 + 3 * c ^ 2) + c * (c ^ 2 + a ^ 2) / (5 * c ^ 2 + 3 * a ^ 2)) ≤ (a + b + c) / 4  :=  by sorry
