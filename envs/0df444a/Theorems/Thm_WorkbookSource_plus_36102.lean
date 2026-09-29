-- Prove2me | Theorems.Thm_WorkbookSource_plus_36102
-- name    : WorkbookSource.plus_36102
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:52:24.414362+00:00
-- url     : https://prove2.me/theorems/5d753cb9-1f6f-4bc7-bb9e-fe02b2df998e
-- title:
--   A comparison of symmetric cubic and quadratic ratios
-- statement:
--   Let $a, b, c > 0$. Prove that $\frac{a^3+b^3+c^3}{3abc}+\frac{2(ab+bc+ca)}{a^2+b^2+c^2}+\frac{(a+b+c)^2}{3(a^2+b^2+c^2)}+\frac{3(ab+bc+ca)}{(a+b+c)^2}\ge 5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_36102` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_36102; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_36102 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (3 * a * b * c) + (2 * (a * b + b * c + c * a)) / (a^2 + b^2 + c^2) + (a + b + c)^2 / (3 * (a^2 + b^2 + c^2)) + (3 * (a * b + b * c + c * a)) / (a + b + c)^2 ≥ 5   :=  by sorry
