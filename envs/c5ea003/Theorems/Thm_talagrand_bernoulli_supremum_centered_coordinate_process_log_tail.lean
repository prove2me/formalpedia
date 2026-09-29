-- Prove2me | Theorems.Thm_talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
-- name    : talagrand_bernoulli_supremum_centered_coordinate_process_log_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T15:39:53.426219+00:00
-- url     : https://prove2.me/theorems/d9fd9c0c-a523-4ada-bdc2-a6e2cbe4b9c4
-- statement:
--   This is the exact product-space Talagrand concentration theorem used in Candès--Recht Appendix 9.1, stated for the finite Bernoulli coordinate process obtained after expanding the tangent sampling operator.
--
--   Let $\Omega\subseteq [n_1]\times[n_2]$ be sampled in the independent Bernoulli model with rate
--   $$p=\frac{m}{n_1n_2}.$$
--   For a finite symmetric class of coefficient arrays $c_a(i,j)$, define
--   $$Z(\Omega)=\sup_a\sum_{i,j}\bigl(1_{(i,j)\in\Omega}-p\bigr)c_a(i,j).$$
--   Assume the class is closed under $c\mapsto -c$, the coordinate increments are bounded by
--   $$|c_a(i,j)|\le B,$$
--   and the variance proxy is bounded by
--   $$\sum_{i,j}p(1-p)c_a(i,j)^2\le \sigma^2.$$
--   Then there is a universal constant $K>0$ such that for every $t\ge0$,
--   $$\mathbb P_p\left(|Z-\mathbb E_pZ|\le t\right)\ge 1-3\exp\left(-\frac{t}{KB}\log\left(1+\frac{Bt}{\sigma^2+B\mathbb E_pZ}\right)\right).$$
--   This is the logarithmic tail in equation (9.2), not the deprecated Gaussian-only shortcut.
--
--   Source location: Candès--Recht Appendix 9.1, PDF p. 46, Theorem 9.1/equation (9.2), citing Talagrand [33] and Ledoux [22, Corollary 7.8].
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion
open scoped Classical BigOperators

theorem talagrand_bernoulli_supremum_centered_coordinate_process_log_tail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) (Z : Finset (Fin n₁ × Fin n₂) → ℝ)
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ Omega,
          Z Omega =
            sSup {v : ℝ |
              ∃ a : ι,
                v =
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) -
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      coeff a i j)}) →
        (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeff a' i j = -coeff a i j) →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Z Omega -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq +
                      B * bernoulliExpectation
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z))) := by
  sorry
