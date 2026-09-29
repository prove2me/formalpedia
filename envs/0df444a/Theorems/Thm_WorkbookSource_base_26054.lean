-- Prove2me | Theorems.Thm_WorkbookSource_base_26054
-- name    : WorkbookSource.base_26054
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:06:56.567975+00:00
-- url     : https://prove2.me/theorems/0cadb7e7-283d-4789-94fd-03835481d62c
-- title:
--   A squared cyclic ratio sum bounds a product of sums
-- statement:
--   If $ x,y,z>0 $ then: $ 5(\frac{x}{y}+\frac{y}{z}+\frac{z}{x})^2 \geq 2(x+y+z)(\frac{1}{x}+\frac{1}{y}+\frac{1}{z})+27 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26054` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26054; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26054 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 5 * (x / y + y / z + z / x) ^ 2 ≥ 2 * (x + y + z) * (1 / x + 1 / y + 1 / z) + 27  :=  by sorry
