-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_moment_from_row_column_energy_2pN
-- name    : rademacher_sampled_matrix_moment_from_row_column_energy_2pN
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T09:40:54.940756+00:00
-- url     : https://prove2.me/theorems/5151e1db-e726-469f-a2ac-ab18f5f5ad23
-- statement:
--   This is the relaxed-window noncommutative Khintchine conversion used in Candès--Recht Section 6.1.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad N=\max(n_1,n_2).
--   $$
--   For a fixed matrix $X\in\mathbb R^{n_1\times n_2}$ and an exponent $q$, assume the sampled row/column energy moment satisfies
--   $$
--   \mathbb E_\Omega\!\left[\max\{E_{\rm row}^{\max}(\Omega,X),E_{\rm col}^{\max}(\Omega,X)\}^{q}\right]
--   \le \left(C_{\rm energy}\,pN\,\|X\|_{\infty}^{2}\right)^q.
--   $$
--   Then there is a universal constant $C_{\rm rad}>0$ such that the Rademacher-signed sampled matrix obeys
--   $$
--   \mathbb E_{\Omega}\mathbb E_{\varepsilon}
--   \left\|R_{\varepsilon}(\Omega,X)\right\|^{q}
--   \le
--   \left(C_{\rm rad}\sqrt{\frac{qN}{p}}\,\|X\|_{\infty}\right)^q.
--   $$
--   Here $R_{\varepsilon}(\Omega,X)$ is the sampled matrix with independent signs on the observed entries and with the same normalization as the Lean definition rademacherSampledMatrix.  The suffix _2pN records that this version assumes only the relaxed exponent window
--   $$
--   q\le 2pN,
--   $$
--   rather than the stricter $q\le pN$ window.  The proof route is exactly the Section 6.1 chain: conditional noncommutative Khintchine, integration over the Bernoulli sample, and the corrected row/column-energy scale-moment bridge.
--
--   Source location for the reduction: Candès--Recht 2008, Section 6.1, PDF pp. 24--25, especially the symmetrization/Khintchine display before Lemma 6.2, Lemma 6.2 and equation (6.6), and the paragraph leading to Theorem 6.3/equation (6.7).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher

open MatrixCompletion

theorem rademacher_sampled_matrix_moment_from_row_column_energy_2pN
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  sorry
