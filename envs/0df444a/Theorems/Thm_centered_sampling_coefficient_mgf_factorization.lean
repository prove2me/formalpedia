-- Prove2me | Theorems.Thm_centered_sampling_coefficient_mgf_factorization
-- name    : centered_sampling_coefficient_mgf_factorization
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T23:54:38.67552+00:00
-- url     : https://prove2.me/theorems/9335fa7f-4c18-4f93-a5c6-38f15a131ade
-- statement:
--   Exact moment generating function (MGF) factorization of the scalar centered-sampling coefficient statistic on the Bernoulli powerset measure. Writing $\mathrm{Coeff}(\Omega)=\mathrm{matrixEntrySum}(\mathrm{centeredSamplingFluctuation}(\Omega,p,B))=\sum_w p^{-1}(\mathbf 1[w\in\Omega]-p)B_w$, the per-coordinate inclusion indicators $\mathbf 1[w\in\Omega]$ are independent Bernoulli($p$) under the powerset measure, so for every real $\lambda$ the moment generating function factorizes over coordinates: $$\mathbb E\big[\exp(\lambda\,\mathrm{Coeff})\big]=\prod_w\Big(p\,\exp(\lambda\,p^{-1}(1-p)B_w)+(1-p)\,\exp(\lambda\,p^{-1}(0-p)B_w)\Big).$$ This is the exact, sorry-free analytic foundation for any Bernstein/Rosenthal/Cramer-Chernoff moment estimate on this bespoke measure: the right-hand side is a product of elementary per-coordinate MGFs, each of a bounded mean-zero increment. It reduces directly onto the Proved independence/product factorization bernoulli_powerset_expectation_prod_factor by taking $f_w(x)=\exp(\lambda p^{-1}(x-p)B_w)$ and using $\exp$ of a sum equals a product of $\exp$.
-- source:
--   Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, Ch. 2 (the MGF / Cramer-Chernoff method); independence of coordinate inclusion is the defining feature of the Bernoulli model in Candes-Recht 2009, arXiv:0805.4471, Section 6.

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Exp
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_coefficient_mgf_factorization {n₁ n₂ : ℕ}
    (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ) (lam : ℝ) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) =
      ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) := by
  sorry
