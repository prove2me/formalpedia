-- Prove2me | Theorems.Thm_lean_workbook_plus_20966
-- name    : lean_workbook_plus_20966
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/424298a4-accc-4590-a493-0f80426ab58e
-- statement:
--   The equation $\sqrt{a^2} = a$ is true only if `a` is nonnegative. If we do not know the sign of $\color[rgb]{0.11,0.21,0.37}a$ , then we cannot simplify $\sqrt{a^2}$ to $a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20966  (a : ℝ) :
  Real.sqrt (a^2) = a ↔ 0 ≤ a   :=  by sorry
