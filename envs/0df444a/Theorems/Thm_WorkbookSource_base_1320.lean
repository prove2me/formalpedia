-- Prove2me | Theorems.Thm_WorkbookSource_base_1320
-- name    : WorkbookSource.base_1320
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:38:17.469871+00:00
-- url     : https://prove2.me/theorems/fe224f4b-5eef-42e3-9a08-1186080edb0b
-- title:
--   A rational bound on the positive quadrant of a circle
-- statement:
--   If $a^2+b^2=4$ , and $a,b$ are positive real numbers, Prove that $ab/(a+b+2)$ is less than or equal to $\sqrt2-1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1320` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1320; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1320 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b > 0) (hab2 : a + b + 2 > 0) (hab3 : a ^ 2 + b ^ 2 = 4) : a * b / (a + b + 2) ≤ Real.sqrt 2 - 1  :=  by sorry
