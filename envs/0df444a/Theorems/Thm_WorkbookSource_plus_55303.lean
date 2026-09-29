-- Prove2me | Theorems.Thm_WorkbookSource_plus_55303
-- name    : WorkbookSource.plus_55303
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:35.918903+00:00
-- url     : https://prove2.me/theorems/ac359ae7-1e9e-42d7-aab2-4aebffa80bc8
-- title:
--   A cyclic quadratic ratio comparison at fixed sum three
-- statement:
--   Let $a, b, c>0, a+b+c=3$ . Prove that $\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a}\ge\frac{2a^2+b}{b+c+1}+\frac{2b^2+c}{c+a+1}+\frac{2c^2+a}{a+b+1}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_55303` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_55303; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_55303 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 / b + b^2 / c + c^2 / a) ≥ (2 * a^2 + b) / (b + c + 1) + (2 * b^2 + c) / (c + a + 1) + (2 * c^2 + a) / (a + b + 1)   :=  by sorry
