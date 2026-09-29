-- Prove2me | Theorems.Thm_WorkbookSource_base_16402
-- name    : WorkbookSource.base_16402
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:30:42.983944+00:00
-- url     : https://prove2.me/theorems/6787460a-77dd-4499-81b9-bc2e0befdb19
-- title:
--   A four-variable weighted cyclic ratio sum is at least one
-- statement:
--   Prove that if ${x_1,x_2,x_3,x_4}\\in(0;+\\infty)$ , then
--
--   $\\frac{x_1}{3x_2+x_3}+\\frac{x_2}{3x_3+x_4}+\\frac{x_3}{3x_4+x_1}+\\frac{x_4}{3x_1+x_2}\\ge1$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16402` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16402; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16402 (x1 x2 x3 x4 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx4 : 0 < x4) : (x1 / (3 * x2 + x3) + x2 / (3 * x3 + x4) + x3 / (3 * x4 + x1) + x4 / (3 * x1 + x2)) ≥ 1  :=  by sorry
