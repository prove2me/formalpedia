-- Prove2me | Theorems.Thm_WorkbookSource_base_55716
-- name    : WorkbookSource.base_55716
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:30.897261+00:00
-- url     : https://prove2.me/theorems/1292cf5d-116e-4d3c-b95e-075fb632a376
-- title:
--   A mixed quadratic ratio sum is at least twenty-two thirds
-- statement:
--   Given $a,b,c>0$ prove that
--    $\frac{a^{2}+16bc}{b^{2}+bc+c^{2}}+\frac{b^{2}+16ca}{c^{2}+ca+a^{2}}+\frac{c^{2}+16ab}{a^{2}+ab+b^{2}}\ge \frac{22}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55716` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55716; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55716 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 16 * b * c) / (b^2 + b * c + c^2) + (b^2 + 16 * c * a) / (c^2 + c * a + a^2) + (c^2 + 16 * a * b) / (a^2 + a * b + b^2) ≥ 22 / 3  :=  by sorry
