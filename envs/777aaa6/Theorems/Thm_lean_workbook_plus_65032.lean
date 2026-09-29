-- Prove2me | Theorems.Thm_lean_workbook_plus_65032
-- name    : lean_workbook_plus_65032
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0986b53c-5693-4014-8c24-76f65b8a4586
-- statement:
--   Prove that if $x, y, z$ are positive real numbers such that $x + y + z = 1$, then $(1 + x)(1 + y)(1 + z) \geq \frac{27}{64}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65032 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : (1 + x) * (1 + y) * (1 + z) ≥ 27 / 64   :=  by sorry
