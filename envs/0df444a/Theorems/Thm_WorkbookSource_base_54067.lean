-- Prove2me | Theorems.Thm_WorkbookSource_base_54067
-- name    : WorkbookSource.base_54067
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:48:47.337253+00:00
-- url     : https://prove2.me/theorems/eda95ca0-28f7-4362-8af8-ff3a6f9ccde7
-- title:
--   A squared pair-product sum bounds a triple-product term
-- statement:
--   Prove that $(xy+yz+zx)^2+3 \geq 12xyz$ given $x+y+z=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54067` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54067; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54067 (x y z : ℝ) (h : x + y + z = 3) :
  (x * y + y * z + z * x) ^ 2 + 3 ≥ 12 * x * y * z  :=  by sorry
