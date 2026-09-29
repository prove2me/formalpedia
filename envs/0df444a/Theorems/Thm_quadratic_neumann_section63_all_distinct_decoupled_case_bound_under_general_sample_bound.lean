-- Prove2me | Theorems.Thm_quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound
-- name    : quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T05:28:26.861384+00:00
-- url     : https://prove2.me/theorems/e78b574a-5850-4617-a03a-a4b06280fa6d
-- statement:
--   This is the fully decoupled three-copy estimate for the all-distinct index case of the five-way partition (6.20) of the second quadratic Neumann correction, from Candes-Recht Section 6.3 (PDF pp. 33-34).
--
--   After the triple decoupling argument, the all-distinct contribution is controlled at the Section 6.3 summary scale Phi.  Concretely, with p = m/(n1 n2), N = max(n1,n2), R = r, and the sampling condition
--   $$ m \ge C' \cdot \max(\mu_1^2,\ \sqrt{\mu_0}\,\mu_1,\ \mu_0 N^{1/4}) \cdot N R\,\beta\log N, $$
--   the operator norm of the decoupled three-sample contribution obeys, with probability at least 1 - c N^{-beta},
--   $$ \|S\| \le C\,\Phi,\quad \Phi = \mu_0^2\mu_1\sqrt{\tfrac{NR\beta\log N}{m}}\Big(\tfrac{NR}{m}\Big)^2 + \mu_0^2\Big(\tfrac{NR}{m}\Big)^2 + \sqrt{\beta\log N}\Big(\tfrac{NR}{m}\Big)^{3/2}\mu_0^2 R + \Big(\tfrac{\mu_0\mu_1 NR\beta\log N}{m}\Big)^{3/2}. $$
--   The proof of this node follows equation (6.23): control the inner G-coefficients via Lemma 6.6, then the middle H-coefficients via a second Lemma 6.6-type estimate, and finally apply Theorem 6.3 in the outer sample.
--
--   Source: Candes-Recht 2008, PDF pp. 33-34, Section 6.3, all-distinct case, equation (6.23) and the summary display.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_all_distinct_decoupled_case_bound_under_general_sample_bound :
    ∃ Cdec cdec : ℝ, 0 < Cdec ∧ 0 < cdec ∧
      ∀ C' : ℝ, Cdec ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cdec *
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
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
