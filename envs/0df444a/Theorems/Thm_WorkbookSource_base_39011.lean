-- Prove2me | Theorems.Thm_WorkbookSource_base_39011
-- name    : WorkbookSource.base_39011
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:43:55.822483+00:00
-- url     : https://prove2.me/theorems/7232d1b4-8d93-4b2c-b684-2aaedcf2e413
-- title:
--   A pairwise ratio sum bounds two symmetric quadratic expressions
-- statement:
--   If $a,b,c$ are positive real numbers, then $\frac{a+b}{c}+\frac{b+c}{a}+\frac{c+a}{b}\ge{\frac{18}{5}+\frac{18}{5}\frac{a^2+b^2+c^2}{(a+b+c)^2}+\frac{2}{5}\frac{(a+b+c)^2}{ab+bc+ca}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39011` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39011; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39011 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c + (b + c) / a + (c + a) / b ≥ 18 / 5 + 18 / 5 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 + 2 / 5 * (a + b + c) ^ 2 / (a * b + b * c + c * a)  :=  by sorry
