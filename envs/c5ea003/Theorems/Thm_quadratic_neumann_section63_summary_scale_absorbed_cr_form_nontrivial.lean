-- Prove2me | Theorems.Thm_quadratic_neumann_section63_summary_scale_absorbed_cr_form_nontrivial
-- name    : quadratic_neumann_section63_summary_scale_absorbed_cr_form_nontrivial
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T19:06:26.0538+00:00
-- url     : https://prove2.me/theorems/8cb28ff8-02a6-4e2c-a63f-b41283a4dc65
-- statement:
--   Corrected Candes-Recht 2008 Section 6.3 scalar absorption: under the Theorem 1.3 sample lower bound (K=max(mu1^2, sqrt(mu0)mu1, mu0 N^{1/4})) and feasibility m<=n1 n2, the CR summary scale Phi_CR (with the Frobenius sqrt(r) third term and the decoupled mu0 mu1 outside the 3/2 power on the fourth term) satisfies Csec*Phi_CR <= 1/8 for C := max 9 ((16 Csec)^{2/3}), for max n1 n2 >= 2.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_summary_scale_absorbed_cr_form_nontrivial
    (Csec : ℝ) :
    0 < Csec →
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        2 ≤ max n₁ n₂ →
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (let N : ℝ := ↑(max n₁ n₂)
         let R : ℝ := (r : ℝ)
         let Mobs : ℝ := (m : ℝ)
         let logN : ℝ := Real.log N
         Csec *
           ((μ₀ ^ 2 * μ₁) *
              Real.sqrt ((N * R * (β * logN)) / Mobs) *
                ((N * R) / Mobs) ^ 2 +
            μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
            Real.sqrt (β * logN) *
                Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                  (μ₀ ^ 2 * Real.sqrt R) +
            μ₀ * μ₁ *
              Real.rpow
                ((N * R * (β * logN)) / Mobs)
                ((3 : ℝ) / 2))) ≤
          (1 : ℝ) / 8 := by
  sorry
