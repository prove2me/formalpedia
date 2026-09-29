-- Prove2me | Theorems.Thm_lean_workbook_plus_69315
-- name    : lean_workbook_plus_69315
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/32cd9ecb-4cec-4f43-9721-cf9bc9e3f719
-- statement:
--   Factor $x^4 - 4x^2 - x + 2$ as $x^2(x^2-4)-(x-2) = (x-2)(x^3+2x^2-1) = (x-2)(x+1)(x^2+x+1)$. These factors are irreducible over $\mathbb{Q}$ and $\mathbb{R}$. The third factor has root $a = \frac{-1+i\sqrt{3}}{2} = \zeta_3$ and factors as $(x-a)(x-a^2)$ over $\mathbb{C}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69315 : ∀ x : ℂ, x^4 - 4 * x^2 - x + 2 = (x - 2) * (x + 1) * (x^2 + x + 1)   :=  by sorry
