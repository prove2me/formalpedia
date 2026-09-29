-- Prove2me | Theorems.Thm_lean_workbook_plus_21271
-- name    : lean_workbook_plus_21271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8b89231a-6572-4dda-99a8-9434b68db36b
-- statement:
--   [0,1] $\subset$ $\mathbb{R}$ is connected.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21271 : IsConnected (Set.Icc (0 : ℝ) 1)   :=  by sorry
