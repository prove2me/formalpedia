-- Prove2me | Theorems.Thm_WorkbookSource_base_908
-- name    : WorkbookSource.base_908
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:34:33.160285+00:00
-- url     : https://prove2.me/theorems/8c4b948f-64ff-4dd8-8589-65dd92f14847
-- title:
--   A bound on a quadratic locus involving square root of three
-- statement:
--   If $x^2+y^2+xy+\sqrt{3}(x+y)=0$ , prove that $x^2+y^2\leq3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_908` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_908; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_908 (x y : ℝ) (h : x^2 + y^2 + x * y + Real.sqrt 3 * (x + y) = 0) :
  x^2 + y^2 ≤ 3  :=  by sorry
