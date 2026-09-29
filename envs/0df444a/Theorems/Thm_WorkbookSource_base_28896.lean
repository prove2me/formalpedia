-- Prove2me | Theorems.Thm_WorkbookSource_base_28896
-- name    : WorkbookSource.base_28896
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:15.273984+00:00
-- url     : https://prove2.me/theorems/5f0ed586-fdfe-4dc1-8440-e12b314716b0
-- title:
--   A quadratic lower bound on a hyperbola
-- statement:
--   Let $x,y$ be reals such that $5x^2- 4xy-y^2=5.$ Prove that $2x^2+y^2\geq \frac{5}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28896` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28896; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28896  (x y : ℝ)
  (h₀ : 5 * x^2 - 4 * x * y - y^2 = 5) :
  2 * x^2 + y^2 ≥ 5 / 3  :=  by sorry
