-- Prove2me | Theorems.Thm_lean_workbook_plus_67149
-- name    : lean_workbook_plus_67149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/f4ba756e-3b73-4d39-bb32-cb1161905d05
-- statement:
--   Showing that all intervals in $\mathbb{R}$ are connected is a fairly standard argument, that relies on the completeness of $\mathbb{R}$. If we cut an interval somewhere, either the bottom side has a greatest element or the top side has a least element.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67149 (u v : ℝ) (huv : u < v) : IsConnected (Set.Icc u v)   :=  by sorry
