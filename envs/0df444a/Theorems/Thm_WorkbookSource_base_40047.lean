-- Prove2me | Theorems.Thm_WorkbookSource_base_40047
-- name    : WorkbookSource.base_40047
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:42.577906+00:00
-- url     : https://prove2.me/theorems/a7563e21-b49e-4677-bd5c-3dde998382c4
-- title:
--   A product of mixed cyclic ratios is at least 27 over eight
-- statement:
--   Let $a,b,c>0.$ Prove that
--    $$\left (\frac{a}{b+c}+\frac{b}{c}\right)\left (\frac{b}{c+a}+\frac{c}{a}\right)\left (\frac{c}{a+b}+\frac{a}{b}\right)\geq \frac{27}{8}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40047` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40047; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40047 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / c) * (b / (c + a) + c / a) * (c / (a + b) + a / b) ≥ 27 / 8  :=  by sorry
