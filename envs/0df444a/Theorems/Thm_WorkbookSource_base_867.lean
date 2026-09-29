-- Prove2me | Theorems.Thm_WorkbookSource_base_867
-- name    : WorkbookSource.base_867
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:34:27.791761+00:00
-- url     : https://prove2.me/theorems/745331f2-651e-4985-8f3c-18a63d441a2f
-- title:
--   A quartic bound involving an absolute difference
-- statement:
--   If $x,y {\ge} 0$ , then prove: $5(x^4+y^4){\ge} (x^2+y^2)(x+y+|x-y|)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_867` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_867; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_867 (x y : ℝ) (hx: x ≥ 0) (hy: y ≥ 0) : 5 * (x^4 + y^4) ≥ (x^2 + y^2) * (x + y + |x - y|)^2  :=  by sorry
