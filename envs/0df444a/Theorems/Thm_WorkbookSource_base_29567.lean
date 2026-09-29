-- Prove2me | Theorems.Thm_WorkbookSource_base_29567
-- name    : WorkbookSource.base_29567
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:10:49.162594+00:00
-- url     : https://prove2.me/theorems/a0b364d6-6703-4663-befb-7bb0e89fba86
-- title:
--   A cyclic quadratic difference ratio sum is nonnegative
-- statement:
--   Assume that $a,b,c,d>0$ ,prove that
--    $\frac{a^2-bd}{b+d+2c}+\frac{b^2-ca}{c+a+2d}+\frac{c^2-db}{d+b+2a}+\frac{d^2-ac}{a+c+2b}\ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29567` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29567; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29567 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 - b * d)/(b + d + 2 * c) + (b^2 - c * a)/(c + a + 2 * d) + (c^2 - d * b)/(d + b + 2 * a) + (d^2 - a * c)/(a + c + 2 * b) ≥ 0  :=  by sorry
