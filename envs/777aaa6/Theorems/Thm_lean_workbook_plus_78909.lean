-- Prove2me | Theorems.Thm_lean_workbook_plus_78909
-- name    : lean_workbook_plus_78909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/dce62f33-0c1a-4a0f-b2ec-82896473d80e
-- statement:
--   $=\dfrac {2n^2 + 2n}{2} - \dfrac {n^2 + n}{2} = \dfrac {n^2 + n}{2} = \dfrac {n(n+1)}{2} = S$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78909  (n : ℕ) :
  ((2 * n^2 + 2 * n) - (n^2 + n)) / 2 = (n^2 + n) / 2   :=  by sorry
