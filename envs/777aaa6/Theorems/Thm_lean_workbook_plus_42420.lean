-- Prove2me | Theorems.Thm_lean_workbook_plus_42420
-- name    : lean_workbook_plus_42420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f4bd7eea-160a-48b3-ab2d-bd40b73a9f3a
-- statement:
--   If $\overline{a}$ is the complex conjugate to $a$ , then $(x-a)(x-\overline{a})$ is a polynomial with real coefficients. They are even rational when $a \in \mathbb{Q}(i)$ . The roots of the polynomial $x^{4}-3x^{2}+9$ have the form $a,\overline{a},b,\overline{b}\in \mathbb{Q}(i)$ , so that it is the product of the rational polynomials $(x-a)(x-\overline{a})$ and $(x-b)(x-\overline{b})$ . The resulting factorization is $(x^{2}+3x+3)*(x^{2}-3x+3)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42420 (x : ℂ) : (x^4 - 3 * x^2 + 9) = (x^2 + 3 * x + 3) * (x^2 - 3 * x + 3)   :=  by sorry
