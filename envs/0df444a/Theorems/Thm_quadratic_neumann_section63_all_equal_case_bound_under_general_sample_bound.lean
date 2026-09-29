-- Prove2me | Theorems.Thm_quadratic_neumann_section63_all_equal_case_bound_under_general_sample_bound
-- name    : quadratic_neumann_section63_all_equal_case_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T17:04:32.022297+00:00
-- url     : https://prove2.me/theorems/83e4a255-ebe0-4dcc-a7ed-790138598a8e
-- statement:
--   This is the all-equal index case $\omega_1=\omega_2=\omega_3$ in the Candes-Recht Section 6.3 five-way partition of the second quadratic Neumann correction.
--
--   Source location: Candes-Recht 2008, Section 6.3, PDF pp. 30--31. Equation (6.21) expands the cubic Bernoulli factor $(\xi_\omega)^3$ into a centered fixed-matrix sampling term and a deterministic mean term. The centered term is controlled by Theorem 6.3 using the entry bound for $H_\omega=E_\omega(p^{-1}P_{\omega\omega})^2$; the mean term is controlled by Lemma 6.4. The paper concludes that this first term of (6.20) is bounded by the first two summands of the Section 6.3 summary display.
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

theorem quadratic_neumann_section63_all_equal_case_bound_under_general_sample_bound :
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
                (quadraticNeumannAllEqualContribution Omega S
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
