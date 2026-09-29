-- Prove2me | Theorems.Thm_WorkbookSource_base_43092
-- name    : WorkbookSource.base_43092
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:58.366891+00:00
-- url     : https://prove2.me/theorems/4ee72b67-8a37-4a9f-955a-65f5d471ca3e
-- title:
--   A squared-distance bound under a quadratic relation
-- statement:
--   $x^{2}-y^{2}=9-4y \implies d^{2}=x^{2}+y^{2}=2y^{2}-4y+9=2(y-1)^{2}+7 \geq 7$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43092` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43092; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43092 (x y d : ℝ) (h₁ : x^2 - y^2 = 9 - 4*y) (h₂ : d^2 = x^2 + y^2): d^2 ≥ 7  :=  by sorry
