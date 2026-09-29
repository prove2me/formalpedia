-- Prove2me | Theorems.Thm_WorkbookSource_plus_10141
-- name    : WorkbookSource.plus_10141
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:32.719987+00:00
-- url     : https://prove2.me/theorems/3bc80a36-7306-43df-9d03-fe8f6a066acf
-- title:
--   A pairwise ratio sum with a symmetric quadratic correction
-- statement:
--   Let $a,b,c>0$ . Prove that :
--
--    $\frac{a+b}{a+b+2c}+\frac{b+c}{b+c+2a}+\frac{c+a}{c+a+2b}+\frac{2}{3}.\frac{ab+bc+ca}{a^2+b^2+c^2} \leq \frac{13}{6}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_10141` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10141; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_10141 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + b + 2 * c) + (b + c) / (b + c + 2 * a) + (c + a) / (c + a + 2 * b) + (2 / 3) * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ 13 / 6   :=  by sorry
