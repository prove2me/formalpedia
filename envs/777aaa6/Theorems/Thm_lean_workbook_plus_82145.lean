-- Prove2me | Theorems.Thm_lean_workbook_plus_82145
-- name    : lean_workbook_plus_82145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/de3129cc-5f11-447f-9d6e-ac7d343faac3
-- statement:
--   1. $x+p\in B_r(x+y)\\iff \\|(x+p)-(x+y)\\|<r\\iff \\|p-y\\|<r\\iff p\in B_r(y)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82145 (x y p : ℝ) (r : ℝ) : x + p ∈ Metric.ball (x + y) r ↔ p ∈ Metric.ball y r   :=  by sorry
