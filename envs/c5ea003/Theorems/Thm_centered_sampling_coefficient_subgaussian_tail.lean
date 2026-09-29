-- Prove2me | Theorems.Thm_centered_sampling_coefficient_subgaussian_tail
-- name    : centered_sampling_coefficient_subgaussian_tail
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T00:33:38.920124+00:00
-- url     : https://prove2.me/theorems/00658a0e-1da6-42af-aaca-d0bacf40a5b8
-- statement:
--   Sub-Gaussian (Hoeffding) tail bound for the centered-sampling coefficient statistic on the Bernoulli powerset measure. For $0<p\le 1$, threshold $0\le t$, and $\lVert B\rVert_F^2>0$, $P(t\le \mathrm{Coeff}) \le \exp(-2p^2t^2/\lVert B\rVert_F^2)$, where $\mathrm{Coeff}(\Omega)=\sum_w p^{-1}(\mathbf 1[w\in\Omega]-p)B_w$ and $P$ is bernoulliEventProb. It is obtained by Cramer-Chernoff optimisation: combine the sub-Gaussian MGF bound $E[\exp(\lambda\,\mathrm{Coeff})]\le\exp(\lambda^2\lVert B\rVert_F^2/(8p^2))$ with the Chernoff tail $P(t\le\mathrm{Coeff})\le\exp(-\lambda t)E[\exp(\lambda\,\mathrm{Coeff})]$, optimised at $\lambda=4p^2t/\lVert B\rVert_F^2$.
-- source:
--   Hoeffding 1963; Boucheron, Lugosi, Massart, Concentration Inequalities, OUP 2013, Ch. 2 (Cramer-Chernoff method); Candes-Recht 2009, arXiv:0805.4471, Section 6.

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Exp
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_coefficient_subgaussian_tail {n₁ n₂ : ℕ}
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hB : 0 < frobeniusNormSq B) :
    bernoulliEventProb p
        (fun Omega =>
          t ≤ matrixEntrySum (centeredSamplingFluctuation Omega p B)) ≤
      Real.exp (-(2 * p ^ 2 * t ^ 2 / frobeniusNormSq B)) := by sorry
