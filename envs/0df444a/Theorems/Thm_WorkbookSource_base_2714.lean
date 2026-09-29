-- Prove2me | Theorems.Thm_WorkbookSource_base_2714
-- name    : WorkbookSource.base_2714
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:02:02.78135+00:00
-- url     : https://prove2.me/theorems/313b107c-06c1-4c73-843e-c5a386f34655
-- title:
--   A symmetric quadratic-product ratio sum bounds the quadratic mean
-- statement:
--   Given $a, b, c > 0$, prove that
--
--   $\frac{ab(a^2+b^2)}{a^2+b^2+ac+bc}+\frac{bc(b^2+c^2)}{b^2+c^2+ba+ca}+\frac{ca(c^2+a^2)}{c^2+a^2+cb+ab}\le \frac{a^2+b^2+c^2}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2714` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2714; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2714 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a * b * (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2 + a * c + b * c) + b * c * (b ^ 2 + c ^ 2) / (b ^ 2 + c ^ 2 + b * a + c * a) + c * a * (c ^ 2 + a ^ 2) / (c ^ 2 + a ^ 2 + c * b + a * b)) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2  :=  by sorry
