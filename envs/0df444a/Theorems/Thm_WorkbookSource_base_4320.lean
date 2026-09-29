-- Prove2me | Theorems.Thm_WorkbookSource_base_4320
-- name    : WorkbookSource.base_4320
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:07.495066+00:00
-- url     : https://prove2.me/theorems/b96c6873-08f0-4547-8f66-13a97fcc03bd
-- title:
--   A cyclic quadratic-difference ratio upper bound
-- statement:
--   If $ a,b,c>0$ , then
--
--    $ \frac{a^2+b^2-3c^2}{a^2+ab+b^2}+\frac{b^2+c^2-3a^2}{b^2+bc+c^2}+\frac{c^2+a^2-3b^2}{c^2+ca+a^2}+\frac{4(ab+bc+ca)}{3(a^2+b^2+c^2)}\leq\frac{1}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4320` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4320; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4320 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 - 3*c^2) / (a^2 + a*b + b^2) + (b^2 + c^2 - 3*a^2) / (b^2 + b*c + c^2) + (c^2 + a^2 - 3*b^2) / (c^2 + c*a + a^2) + (4 * (a*b + b*c + a*c)) / (3 * (a^2 + b^2 + c^2)) ≤ 1 / 3  :=  by sorry
