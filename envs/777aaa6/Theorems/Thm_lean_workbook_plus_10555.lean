-- Prove2me | Theorems.Thm_lean_workbook_plus_10555
-- name    : lean_workbook_plus_10555
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/77ad7044-10a7-4951-b19a-247bb11e16ca
-- statement:
--   Prove that $\left||a|-|b|\right|\le |a-b|$ for all $a,b\in\mathbb{R}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10555 (a b : ℝ) : |(abs a) - (abs b)| ≤ abs (a - b)   :=  by sorry
