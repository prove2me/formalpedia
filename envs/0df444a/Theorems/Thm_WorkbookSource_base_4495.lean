-- Prove2me | Theorems.Thm_WorkbookSource_base_4495
-- name    : WorkbookSource.base_4495
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:33.63962+00:00
-- url     : https://prove2.me/theorems/102237f4-f090-4ab7-8d0a-d582b9cf1462
-- title:
--   A quartic lower bound with mixed and linear terms
-- statement:
--   Prove that \(x^4 + 5 + y^2 + y^4 \ge x^2 + 4y +2xy^2\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4495` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4495; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4495 (x y : ℝ) : x^4 + 5 + y^2 + y^4 ≥ x^2 + 4*y + 2*x*y^2  :=  by sorry
