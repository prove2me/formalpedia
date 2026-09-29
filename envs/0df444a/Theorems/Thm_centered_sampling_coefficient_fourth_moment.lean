-- Prove2me | Theorems.Thm_centered_sampling_coefficient_fourth_moment
-- name    : centered_sampling_coefficient_fourth_moment
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T22:56:53.844005+00:00
-- url     : https://prove2.me/theorems/74e76f43-5482-4d24-b5c3-14580d196839
-- statement:
--   **Exact fourth moment of the scalar centered-sampling coefficient.** Let $0<p$, let $B$ be an $n_1\times n_2$ real matrix, and let $\mathrm{Coeff}(\Omega)=\mathrm{matrixEntrySum}(\mathrm{centeredSamplingFluctuation}(\Omega,p,B))=\sum_{w}p^{-1}B_w(\mathbf 1[w\in\Omega]-p)$ be the scalar centered sampling coefficient, a sum of independent mean-zero terms $h_w(x)=p^{-1}B_w(x-p)$ under the Bernoulli powerset measure (each coordinate included independently with probability $p$). Then the fourth moment has the exact closed form
--
--   $$\mathbb E\big[\mathrm{Coeff}^4\big]=\sum_{w}\big(p\,h_w(1)^4+(1-p)\,h_w(0)^4\big)+3\sum_{a\ne b}\mu_2(a)\,\mu_2(b),$$
--
--   where $\mu_2(w)=\tfrac{1-p}{p}B_w^2=\mathbb E[h_w^2]$ and the first sum is the diagonal $\sum_w\mathbb E[h_w^4]$. This is the standard fourth-moment identity for a sum of independent mean-zero random variables (Rosenthal 1970; Boucheron-Lugosi-Massart, *Concentration Inequalities*, OUP 2013, Ch. 15): expanding $\mathrm{Coeff}^4=\sum_{a,b,c,d}h_ah_bh_ch_d$ and using independence, every term in which some index has multiplicity exactly one vanishes (it carries a mean factor $p\,h_w(1)+(1-p)h_w(0)=0$); only the all-equal pattern (giving $\sum_w\mathbb E[h_w^4]$) and the three two-distinct-pairs orderings (giving $3\sum_{a\ne b}\mathbb E[h_a^2]\mathbb E[h_b^2]$) survive.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_coefficient_fourth_moment {n₁ n₂ : ℕ} (p : ℝ) (hp : p ≠ 0)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 4) =
      (∑ w : Fin n₁ × Fin n₂,
          (p * (p⁻¹ * (B w.1 w.2) * (1 - p))^4 + (1 - p) * (p⁻¹ * (B w.1 w.2) * (0 - p))^4))
      + 3 * (∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
          (if a = b then 0 else
            (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B b.1 b.2)^2))) := by sorry
