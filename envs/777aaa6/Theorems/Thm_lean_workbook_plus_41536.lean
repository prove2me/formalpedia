-- Prove2me | Theorems.Thm_lean_workbook_plus_41536
-- name    : lean_workbook_plus_41536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/460afc72-5763-46b0-8043-bb49a83dd5fd
-- statement:
--   Show that $x+\frac{1}{x}-(y+\frac{1}{y}) \geq 0$ for $x \geq y \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41536  (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x ≥ y) :
  x + 1/x - (y + 1/y) ≥ 0   :=  by sorry
