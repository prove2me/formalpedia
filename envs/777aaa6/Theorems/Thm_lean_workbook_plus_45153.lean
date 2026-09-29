-- Prove2me | Theorems.Thm_lean_workbook_plus_45153
-- name    : lean_workbook_plus_45153
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/50df463c-d5a2-4775-8365-f675cfa1717b
-- statement:
--   Prove that for all positive real numbers $x$, $y$, and $z$, the following inequality holds: $\sum_{cyc}x^{4}+2x^{2}y^{2}\ge\sum_{cyc}2yx^{3}+y^{3}x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45153 (x y z : ℝ) : (x^4 + y^4 + z^4) + 2 * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ≥ (2 * (x^3 * y + y^3 * z + z^3 * x)) + (x * y^3 + y * z^3 + z * x^3)   :=  by sorry
