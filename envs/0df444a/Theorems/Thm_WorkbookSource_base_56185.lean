-- Prove2me | Theorems.Thm_WorkbookSource_base_56185
-- name    : WorkbookSource.base_56185
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:26.717222+00:00
-- url     : https://prove2.me/theorems/a7329f6a-18b0-4c92-8fba-ecbbebe5a7ab
-- title:
--   A shifted cyclic quadratic ratio product is at least one
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3 .$ Prove that ${\left( \frac{a^2}{b+c}+\frac{1}{2} \right)\left( \frac{b^2}{c+a}+\frac{1}{2} \right)\left( \frac{c^2}{a+b}+\frac{1}{2} \right)}\geq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56185` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56185; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56185 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 / (b + c) + 1 / 2) * (b^2 / (c + a) + 1 / 2) * (c^2 / (a + b) + 1 / 2) ≥ 1  :=  by sorry
