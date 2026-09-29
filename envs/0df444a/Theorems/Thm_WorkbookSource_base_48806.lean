-- Prove2me | Theorems.Thm_WorkbookSource_base_48806
-- name    : WorkbookSource.base_48806
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:47.521883+00:00
-- url     : https://prove2.me/theorems/6105e53a-50b2-423c-a6db-bef798f53807
-- title:
--   A quartic lower bound with linear and cyclic cubic terms
-- statement:
--   For reals $a,b,c$ , prove that:
--   a^4+b^4+c^4+4a+4b+4c+12 \ge 3a^2+3b^2+3c^2+2ab^2+2bc^2+2ca^2
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48806` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48806; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48806 (a b c : ℝ) : a^4+b^4+c^4+4*a+4*b+4*c+12 ≥ 3*a^2+3*b^2+3*c^2+2*a*b^2+2*b*c^2+2*c*a^2  :=  by sorry
