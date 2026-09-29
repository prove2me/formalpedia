-- Prove2me | Theorems.Thm_quadratic_neumann_section63_middle_index_distinct_case_bound_under_general_sample_bound
-- name    : quadratic_neumann_section63_middle_index_distinct_case_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T17:05:17.166604+00:00
-- url     : https://prove2.me/theorems/19ea496a-1231-4de4-ac28-4a055aa5488c
-- statement:
--   This is the index-coincidence case $\omega_1=\omega_3\ne\omega_2$ in the Candes-Recht Section 6.3 five-way partition (6.20).
--
--   Source location: Candes-Recht 2008, Section 6.3, PDF pp. 32--33. The paper decouples the centered part, estimates the auxiliary coefficients $H_{\omega_1}$ by Bernstein using $|P_{\omega_2\omega_1}|\le2\mu_0r/n$, and then applies Theorem 6.3. The non-centered term is controlled in Frobenius norm by $\|H\|_\infty\|E\|_F$. The resulting bound is one of the contributions folded into the PDF p. 34 summary display.
--
--   The bound is stated at the same final Section 6.3 summary scale
--   $$
--   \Phi=(\mu_0^2\mu_1)\sqrt{\frac{nr\,\beta\log n}{m}}\left(\frac{nr}{m}\right)^2
--   +\mu_0^2\left(\frac{nr}{m}\right)^2
--   +\sqrt{\beta\log n}\left(\frac{nr}{m}\right)^{3/2}\mu_0^2 r
--   +\left(\frac{\mu_0\mu_1nr\,\beta\log n}{m}\right)^{3/2}.
--   $$
--   Thus the theorem asserts that this single case has spectral norm at most $C\Phi$ with probability at least $1-cn^{-\beta}$ under the full Theorem 1.3 sample lower bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_middle_index_distinct_case_bound_under_general_sample_bound :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 C *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
