-- Prove2me | Theorems.Thm_lean_workbook_plus_59417
-- name    : lean_workbook_plus_59417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/677d7975-4bf1-4829-a088-8670cac8cac7
-- statement:
--   It is given that one root of $ 2x^2 + rx + s = 0$ , with $ r$ and $ s$ real numbers, is $ 3 + 2i (i = \sqrt { - 1})$ . The value of $ s$ is: \n\n $ \textbf{(A)}\ \text{undetermined} \qquad \textbf{(B)}\ 5 \qquad \textbf{(C)}\ 6 \qquad \textbf{(D)}\ - 13 \qquad \textbf{(E)}\ 26$ \n\nSince the coefficients of the quadratic are real, the other root is $ 3-2i$ and the product of the roots is $ \frac{s}{2}=(3+2i)(3-2i)=9+4=13$ . \n\n $ s=26$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59417  (r s : ℝ)
  (f : ℂ → ℂ)
  (h₀ : ∀ z, f z = 2 * z^2 + r * z + s)
  (h₁ : f (3 + 2 * Complex.I) = 0) :
  s = 26   :=  by sorry
