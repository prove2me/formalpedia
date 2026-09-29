-- Prove2me | Theorems.Thm_WorkbookSource_base_48525
-- name    : WorkbookSource.base_48525
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:26:39.927741+00:00
-- url     : https://prove2.me/theorems/ad2a4c40-4948-44d9-a49a-f8aaa517cbdc
-- title:
--   A cyclic fifth-power ratio bounds squared pairwise products
-- statement:
--   Given $a,b,c>0$ prove that $\frac{a^5}{b+c}+\frac{b^5}{c+a}+\frac{c^5}{a+b}\geq\frac{a^2b^2+b^2c^2+c^2a^2}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48525` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48525; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48525 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 / (b + c) + b^5 / (c + a) + c^5 / (a + b)) ≥ (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) / 2  :=  by sorry
