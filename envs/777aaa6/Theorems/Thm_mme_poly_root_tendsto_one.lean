-- Prove2me | Theorems.Thm_mme_poly_root_tendsto_one
-- name    : mme_poly_root_tendsto_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-28T20:42:40.748784+00:00
-- url     : https://prove2.me/theorems/3d9eab5e-a1f5-4aaa-9a3a-a902b9abffbb
-- statement:
--   **Polynomial roots tend to one.** For naturals $a,b$, the $(n+1)$-th root of $((n+1)a+1)^b$ tends to $1$: $((n+1)a+1)^{b/(n+1)}\to1$. The base grows polynomially while the exponent $\to0$, so any polynomial overhead is annihilated in the limit.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open Filter Topology

theorem mme_poly_root_tendsto_one (a b : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((((n + 1) * a + 1) ^ b : ℕ) : ℝ) ^ ((1 : ℝ) / (n + 1)))
      Filter.atTop (nhds 1) := by sorry
