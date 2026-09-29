-- Prove2me | Theorems.Thm_WorkbookSource_base_14266
-- name    : WorkbookSource.base_14266
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:54:34.722616+00:00
-- url     : https://prove2.me/theorems/7a40deda-aeb2-4055-a1d9-e4ee7042daf5
-- title:
--   A cyclic ratio sum with an asymmetric quadratic correction
-- statement:
--   Let $a,b,c>0$. Prove that $\frac{a}{b}+\frac{b}{c}+\frac{c}{a}+\frac{2ab}{a^2+b^2} \geq 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14266` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14266; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14266 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a + 2 * a * b / (a ^ 2 + b ^ 2) ≥ 4  :=  by sorry
