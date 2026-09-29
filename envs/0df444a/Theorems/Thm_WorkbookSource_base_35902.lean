-- Prove2me | Theorems.Thm_WorkbookSource_base_35902
-- name    : WorkbookSource.base_35902
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:08:57.81193+00:00
-- url     : https://prove2.me/theorems/d859f0f6-db57-4d17-b95d-41af36cb56a9
-- title:
--   A pairwise ratio sum bounded by cyclic ratios
-- statement:
--   Prove(using only AM-GM if possible) that for a,b,c>0
--    $\sum_{cyc}\frac{c}{a+b}\leq\frac{3}{2}\left(\frac{a}{b}+\frac{b}{c}+\frac{c}{a}-2\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35902` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35902; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35902 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c / (a + b) + b / (a + c) + a / (b + c)) ≤ (3 / 2) * (a / b + b / c + c / a - 2)  :=  by sorry
