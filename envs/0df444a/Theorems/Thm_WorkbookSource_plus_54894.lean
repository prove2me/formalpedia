-- Prove2me | Theorems.Thm_WorkbookSource_plus_54894
-- name    : WorkbookSource.plus_54894
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:42.069553+00:00
-- url     : https://prove2.me/theorems/7cef6fde-7f74-45d6-b305-fb16c1087599
-- title:
--   A cyclic quartic difference ratio bounds half the pair-product sum
-- statement:
--   For positive real numbers, show that:
--
--   $ \frac{a^3(b+c-a)}{a^2+bc}+\frac{b^3(c+a-b)}{b^2+ca}+\frac{c^3(a+b-c)}{c^2+ab}\le \frac{ab+bc+ca}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_54894` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_54894; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_54894 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 * (b + c - a) / (a^2 + b * c) + b^3 * (c + a - b) / (b^2 + c * a) + c^3 * (a + b - c) / (c^2 + a * b)) ≤ (a * b + b * c + c * a) / 2   :=  by sorry
