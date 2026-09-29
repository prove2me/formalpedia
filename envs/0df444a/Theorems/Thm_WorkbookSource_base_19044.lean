-- Prove2me | Theorems.Thm_WorkbookSource_base_19044
-- name    : WorkbookSource.base_19044
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:38:47.104237+00:00
-- url     : https://prove2.me/theorems/3f7dcdcd-a273-49ec-be72-319143ad240c
-- title:
--   A product of sums bounds two symmetric quadratic ratios
-- statement:
--   If $a,b,c$ are positive real numbers, then $(a+b+c)\left ( \frac{1}{a}+\frac{1}{b}+\frac{1}{c} \right ) \geqslant{\frac{27}{2}\frac{a^2+b^2+c^2}{(a+b+c)^2}+\frac{3}{2}\frac{(a+b+c)^2}{ab+bc+ca}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19044` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19044; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19044 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ (27 / 2 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 + 3 / 2 * (a + b + c) ^ 2 / (a * b + b * c + a * c))  :=  by sorry
