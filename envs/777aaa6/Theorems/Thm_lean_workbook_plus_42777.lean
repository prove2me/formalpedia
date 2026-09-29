-- Prove2me | Theorems.Thm_lean_workbook_plus_42777
-- name    : lean_workbook_plus_42777
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a7c93608-0a4b-4d63-9494-a2f2721ff09d
-- statement:
--   Let x+y=S, xy=P ( $ S^{2}\geq 4P $ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42777 {x y S P : ℝ} (hx : x + y = S) (hy : x * y = P) : S^2 ≥ 4 * P   :=  by sorry
