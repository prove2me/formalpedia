-- Prove2me | Theorems.Thm_lean_workbook_plus_81512
-- name    : lean_workbook_plus_81512
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/fed2b3d5-f2aa-4cc9-b3fd-93ec56022b95
-- statement:
--   $(x-y)^2 \mid x^2+y^2 \Longrightarrow (x-y)^2 \mid 2xy$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81512 (x y : ℤ) : (x - y) ^ 2 ∣ x ^ 2 + y ^ 2 → (x - y) ^ 2 ∣ 2 * x * y   :=  by sorry
