-- Prove2me | Theorems.Thm_lean_workbook_plus_2465
-- name    : lean_workbook_plus_2465
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/19a7876f-b137-4e52-800d-f6af781f509d
-- statement:
--   To prove right inequality we have to prove: \n $ (x+z)^2-4y(x+z)+4y^2 \ge 0$ \n $ \Leftrightarrow$ $ (x+z-2y)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2465 (x y z : ℝ) : (x + z) ^ 2 - 4 * y * (x + z) + 4 * y ^ 2 ≥ 0   :=  by sorry
