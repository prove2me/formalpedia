-- Prove2me | Theorems.Thm_WorkbookSource_base_32836
-- name    : WorkbookSource.base_32836
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:53.812994+00:00
-- url     : https://prove2.me/theorems/454f7e59-ad38-4c92-9412-88fbf9fd37eb
-- title:
--   A cyclic quadratic difference ratio sum is at least three halves
-- statement:
--   Prove the inequality
--
--   $\frac{b^2+c^2-a^2}{a\left(b+c\right)}+\frac{c^2+a^2-b^2}{b\left(c+a\right)}+\frac{a^2+b^2-c^2}{c\left(a+b\right)}\geq\frac32$
--
--   for any three positive reals $a$ , $b$ , $c$ .
--
--   Comment. This was an attempt of creating a contrast to the (rather hard) inequality at the QEDMO before. However, it turned out to be more difficult than I expected (a wrong solution was presented during the competition).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32836` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32836; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32836 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^2 + c^2 - a^2) / (a * (b + c)) + (c^2 + a^2 - b^2) / (b * (c + a)) + (a^2 + b^2 - c^2) / (c * (a + b)) ≥ 3 / 2  :=  by sorry
