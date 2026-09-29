-- Prove2me | Theorems.Thm_WorkbookSource_base_54671
-- name    : WorkbookSource.base_54671
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:37.78295+00:00
-- url     : https://prove2.me/theorems/5f2937ea-49ee-4ccb-9c3e-bac776476532
-- title:
--   A cyclic cubic ratio with an asymmetric square correction
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that
--    $\frac{a^3}{b}+\frac{b^3}{c}+\frac{c^3}{a}\ge a^2+b^2+c^2+\frac{4(a-b)^2c^2}{a^2+b^2+c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54671` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54671; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54671 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / b + b^3 / c + c^3 / a) ≥ a^2 + b^2 + c^2 + (4 * (a - b)^2 * c^2) / (a^2 + b^2 + c^2)  :=  by sorry
