-- Prove2me | Theorems.Thm_centered_sampling_coefficient_fourth_moment_bound
-- name    : centered_sampling_coefficient_fourth_moment_bound
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T23:13:25.889204+00:00
-- url     : https://prove2.me/theorems/b16d529b-9f0d-4e1f-953e-6c64cdc87cd7
-- statement:
--   **Bernstein/Rosenthal fourth-moment bound for the scalar centered-sampling coefficient.** With $0<p\le1$, $B$ an $n_1\times n_2$ real matrix and $\mathrm{Coeff}(\Omega)=\sum_w p^{-1}B_w(\mathbf 1[w\in\Omega]-p)$ a sum of independent mean-zero terms $h_w$ under the Bernoulli powerset measure,
--
--   $$\mathbb E[\mathrm{Coeff}^4]\le 3\,\big(\mathbb E[\mathrm{Coeff}^2]\big)^2+\sum_w p^{-3}(1-p)B_w^4.$$
--
--   The first term $3(\mathbb E[\mathrm{Coeff}^2])^2=3(\sigma^2)^2$ is the Gaussian (Wick/pairing) leading term — the $(2\cdot2-1)!!=3$ pairings of four indices into two pairs — and $\sigma^2=\mathbb E[\mathrm{Coeff}^2]=\frac{1-p}{p}\lVert B\rVert_F^2$. The second term is the diagonal (fourth-cumulant / almost-sure) contribution $\sum_w\mathbb E[h_w^4]\le\sum_w p^{-3}(1-p)B_w^4$. This is the $q=4$ case of the moment form of Bernstein's inequality (Boucheron-Lugosi-Massart, *Concentration Inequalities*, OUP 2013, Ch. 15; Rosenthal 1970).

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_coefficient_fourth_moment_bound {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 4) ≤
      3 * (bernoulliExpectation p
            (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 2)) ^ 2
      + ∑ w : Fin n₁ × Fin n₂, p⁻¹^3 * (1 - p) * (B w.1 w.2)^4 := by sorry
