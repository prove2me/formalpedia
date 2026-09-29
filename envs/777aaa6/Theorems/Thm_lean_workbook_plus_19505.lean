-- Prove2me | Theorems.Thm_lean_workbook_plus_19505
-- name    : lean_workbook_plus_19505
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/63e49e56-72eb-4069-849c-4bb23cc1d197
-- statement:
--   Prove that for all positive real numbers $x$, $y$, and $z$, the following inequality holds:\n$\sum\frac{xy^{2}}{y+z}\ge \frac{xy+yz+zx}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19505 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y ^ 2 / (y + z) + y * z ^ 2 / (z + x) + z * x ^ 2 / (x + y)) ≥ (x * y + y * z + z * x) / 2   :=  by sorry
