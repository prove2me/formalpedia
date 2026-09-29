-- Prove2me | Theorems.Thm_lean_workbook_plus_59183
-- name    : lean_workbook_plus_59183
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/da038305-317d-440d-957c-217021079a3f
-- statement:
--   Does $ f(x) = \left\{ \begin{array}{ll} f(x) = 0 & x \ne \frac12 \ f(x) = \frac12 & x = \frac12 \end{array} \right.$ work? The discontinuity is removable and the integral should still be a $ 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59183 ∀ x, x ≠ 1/2 ∨ x = 1/2 → (if x ≠ 1/2 then 0 else 1/2) = 0   :=  by sorry
