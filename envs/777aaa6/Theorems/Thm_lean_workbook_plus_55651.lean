-- Prove2me | Theorems.Thm_lean_workbook_plus_55651
-- name    : lean_workbook_plus_55651
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4fec1227-33d3-410a-8a20-e631a2e12d5c
-- statement:
--   Let $0 <y<x\leq 3$ and $x+y \leq 5$ . Prove $x^2+y^2 \leq 13$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55651 (x y : ℝ) (h1 : 0 < y ∧ y < x ∧ x ≤ 3) (h2 : x + y ≤ 5) : x^2 + y^2 ≤ 13   :=  by sorry
