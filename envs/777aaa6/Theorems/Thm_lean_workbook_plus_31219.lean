-- Prove2me | Theorems.Thm_lean_workbook_plus_31219
-- name    : lean_workbook_plus_31219
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0683c967-1d86-4be8-8f93-b56031e7fdc4
-- statement:
--   Positive numbers $x, y, z$ satisfy $x^2+y^2+z^2+xy+yz+zx \le 1$ . Prove that $\big( \frac{1}{x}-1\big) \big( \frac{1}{y}-1\big)\big( \frac{1}{z}-1\big) \ge 9 \sqrt6 -19$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31219 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) (h' : x^2 + y^2 + z^2 + x * y + x * z + y * z ≤ 1) : (1 - x) * (1 - y) * (1 - z) ≥ 9 * Real.sqrt 6 - 19   :=  by sorry
