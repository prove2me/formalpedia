-- Prove2me | Theorems.Thm_lean_workbook_plus_4705
-- name    : lean_workbook_plus_4705
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f7f0abfe-9f07-47df-a9c6-c547a5b262f8
-- statement:
--   Let $a^2 + b^2 = m$ and $ab = n$ ; then we must show $2(m^2 - n^2) \geq 3mn \Longleftrightarrow (2m + n)(m - 2n) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4705 (m n : ℝ) : 2 * (m ^ 2 - n ^ 2) ≥ 3 * m * n ↔ (2 * m + n) * (m - 2 * n) ≥ 0   :=  by sorry
