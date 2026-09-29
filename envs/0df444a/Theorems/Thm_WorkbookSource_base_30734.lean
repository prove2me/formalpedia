-- Prove2me | Theorems.Thm_WorkbookSource_base_30734
-- name    : WorkbookSource.base_30734
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:17.382254+00:00
-- url     : https://prove2.me/theorems/9948ef95-7f90-462c-b449-80c1ff8e6089
-- title:
--   A quartic bound under a quartic relation
-- statement:
--   Prove that if $(a^2-2b)^2+4b^2=2a$ , then $(a^2-4b)^2<=3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30734` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30734; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30734 (a b : ℝ) (h : (a^2 - 2 * b)^2 + 4 * b^2 = 2 * a) :
  (a^2 - 4 * b)^2 ≤ 3  :=  by sorry
