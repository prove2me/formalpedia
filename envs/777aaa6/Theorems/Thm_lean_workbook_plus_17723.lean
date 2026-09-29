-- Prove2me | Theorems.Thm_lean_workbook_plus_17723
-- name    : lean_workbook_plus_17723
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/852ea98f-1110-4231-9ca2-2bab447077f8
-- statement:
--   Given $ x \ge y \ge 0$ , that is\n\n$ \frac{x}{1+y} \ge \frac{y}{y+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17723 (x y : ℝ) (hxy : x ≥ y) (hy : y ≥ 0) : (x / (1 + y)) ≥ (y / (y + 1))   :=  by sorry
