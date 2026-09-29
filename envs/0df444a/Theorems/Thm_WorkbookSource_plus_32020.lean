-- Prove2me | Theorems.Thm_WorkbookSource_plus_32020
-- name    : WorkbookSource.plus_32020
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:21.437153+00:00
-- url     : https://prove2.me/theorems/62f45bc7-fa97-4a67-af43-230eef4be1b1
-- title:
--   A floor-function equation has no positive solution
-- statement:
--   Prove that there's no real positive solutions for $x + 2022 = \lfloor x \rfloor \cdot \{ x \}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_32020` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32020; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_32020 (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x))   :=  by sorry
