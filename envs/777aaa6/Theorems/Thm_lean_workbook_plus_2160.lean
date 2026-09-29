-- Prove2me | Theorems.Thm_lean_workbook_plus_2160
-- name    : lean_workbook_plus_2160
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/afddf68e-85ff-4faa-b126-baffac55c23a
-- statement:
--   For the second difference equation, y_{n+1} - 2 y_n = n ,\nApplying the z-transform to both sides we get\n$ \mathcal{Z}(y_{n+1}) - 2 \mathcal{Z}(y_n) = \mathcal{Z}(n)$\n$ => z[Y(z) - y_0] - 2 Y(z) = \frac{z}{(z-1)^2}$\nand solving for Y(z) we get\n$ Y(z) = y_0 + \frac{2y_0z^2 + (1-4y_0)z + 2y_0}{(z-2)(z-1)^2} = y_0 + \frac{2+2y_0}{z-2} - \frac{1}{(z-1)^2} - \frac{2}{z-1}$ .\nNow let's find the inverse z-transform of each term:\n$ y_n = \mathcal{Z} ^{-1}(y_0) + (2+2y_0) \mathcal{Z} ^{-1}\left(\frac{1}{z-2}\right) - \mathcal{Z} ^{-1} \left(\frac{1}{(z-1)^2}\right) - 2 \mathcal{Z} ^{-1}\left(\frac{1}{z-1}\right)$\n$ => y_n = y_0 \delta_n + (2+2y_0) 2^{n-1} u_{n-1} - (n-1) u_{n-1} - 2 u_{n-1}$ .\nFor n=0, we get $ y_n = y_0$ , and for $ n \geq 1$ we have\n$ y_n = (1+y_0)2^n - n + 1 - 2 => y_n = (1+y_0)2^n - n -1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2160  (y : ℕ → ℝ)
  (n : ℕ)
  (h₀ : y 0 = y_0)
  (h₁ : ∀ n, y (n + 1) - 2 * y n = n) :
  y n = (1 + y 0) * 2^n - n - 1   :=  by sorry
