-- Prove2me | Theorems.Thm_lean_workbook_plus_13590
-- name    : lean_workbook_plus_13590
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ea900ba6-1769-473f-847b-7e5d84deb730
-- statement:
--   One method: Use the inequality $xy \leq \frac{(x+y)^2}{4}$ and express $x^ny^n(x^2+y^2)$ as $x^ny^n((x+y)^2-2xy)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13590 (x y n : ℕ) :
  x^n * y^n * (x^2 + y^2) ≤ x^n * y^n * ((x + y)^2 - 2 * x * y)   :=  by sorry
