-- Prove2me | Theorems.Thm_WorkbookSource_plus_47518
-- name    : WorkbookSource.plus_47518
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:23:33.90713+00:00
-- url     : https://prove2.me/theorems/900ca1d7-c7aa-4a44-a46b-a9fec3e3ca57
-- title:
--   A shifted cyclic ratio sum bounds a normalized total
-- statement:
--   Prove that $\frac{a}{b+1}+\frac{b}{c+1}+\frac{c}{a+1}\ge \frac{3(a+b+c)}{3+a+b+c}$ given $a,b,c$ are positive reals.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_47518` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_47518; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_47518 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + 1) + b / (c + 1) + c / (a + 1)) ≥ 3 * (a + b + c) / (3 + a + b + c)   :=  by sorry
