-- Prove2me | Theorems.Thm_lean_workbook_plus_22572
-- name    : lean_workbook_plus_22572
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f033e332-c3da-4302-8d00-37dedfdfa24f
-- statement:
--   We can sum up each of the voltage drops to get the total voltage drop. However, since one of the cells is reversed, we subtract that one instead of adding. $V_{total}=3 \cdot 1.5 - 1.5=3 \; V$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22572  (v : ℝ)
  (h₀ : v = 3 * 1.5 - 1.5) :
  v = 3   :=  by sorry
