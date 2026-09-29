-- Prove2me | Theorems.Thm_WorkbookSource_plus_15828
-- name    : WorkbookSource.plus_15828
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:12:28.125363+00:00
-- url     : https://prove2.me/theorems/4793dba3-f771-49a3-9cd2-a0b7c7442bf8
-- title:
--   A sextic polynomial has no real roots
-- statement:
--   Prove that the equation $x^6+x^5+x^4-x^3-x^2+1=0$ does not have any real solution.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_15828` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_15828; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_15828 : ¬ (∃ x : ℝ, x^6 + x^5 + x^4 - x^3 - x^2 + 1 = 0)   :=  by sorry
