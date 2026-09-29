-- Prove2me | Theorems.Thm_lean_workbook_plus_69485
-- name    : lean_workbook_plus_69485
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0c502b57-ceef-483b-807a-456a5ec71a9d
-- statement:
--   Prove that $||nx||\leq |n|\cdot||x||$ holds for any real $x$ and integer $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69485 (n : ℤ) (x : ℝ) : ‖(n : ℝ) • x‖ ≤ |(n : ℝ)| • ‖x‖   :=  by sorry
