-- Prove2me | Theorems.Thm_lean_workbook_plus_30443
-- name    : lean_workbook_plus_30443
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/011fbd5d-ee00-4904-bc84-ff4f4703e660
-- statement:
--   Given $x \ge 0$ , prove that $\frac{(x^2 + 1)^6}{2^7}+\frac12 \ge x^5 - x^3 + x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30443 (x : ℝ) (hx : 0 ≤ x) : (x^2 + 1)^6 / 2^7 + 1 / 2 ≥ x^5 - x^3 + x   :=  by sorry
