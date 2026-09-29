-- Prove2me | Theorems.Thm_WorkbookSource_base_18914
-- name    : WorkbookSource.base_18914
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:50.932988+00:00
-- url     : https://prove2.me/theorems/2d1691a6-d4b7-451f-bb2e-828ee40769e9
-- title:
--   A cyclic ratio sum with a symmetric quadratic correction
-- statement:
--   If $ a,b,c>0 $ prove or disprove that: $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}+2\frac{bc+ca+ab}{a^2+b^2+c^2}\ge 5 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18914` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18914; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18914 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + (2 * (b * c + c * a + a * b)) / (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 5  :=  by sorry
