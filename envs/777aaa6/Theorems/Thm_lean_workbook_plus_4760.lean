-- Prove2me | Theorems.Thm_lean_workbook_plus_4760
-- name    : lean_workbook_plus_4760
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e1474c8f-7374-4006-91fd-c7c673c8b877
-- statement:
--   Let $X=(0,1) \in \mathbb{R}$ with the usual metric. Then $S=[0,1)$ is not closed.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4760 : ¬IsClosed (Set.Ico (0 : ℝ) 1)   :=  by sorry
