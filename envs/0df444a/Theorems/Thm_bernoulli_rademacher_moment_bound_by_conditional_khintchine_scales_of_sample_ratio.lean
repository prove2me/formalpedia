-- Prove2me | Theorems.Thm_bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
-- name    : bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T19:32:33.641305+00:00
-- url     : https://prove2.me/theorems/48ccbfdf-42f9-49aa-8d70-5d6ae0af91da
-- statement:
--   Sample-ratio-safe integration of the conditional noncommutative Khintchine estimate over the Bernoulli observation set.
--
--   Let
--   $$
--   p={m\over n_1n_2},\qquad 0<n_1,\quad 0<n_2,\quad m\le n_1n_2.
--   $$
--   These hypotheses imply $0\le p\le1$, so the Bernoulli weights
--   $$
--   p^{|\Omega|}(1-p)^{n_1n_2-|\Omega|}
--   $$
--   are nonnegative. Therefore a pointwise conditional estimate
--   $$
--   \mathbb E_\varepsilon\,\|S_\varepsilon(\Omega)\|^q
--   \le
--   \left(C_{\rm Kh}\sqrt q\,p^{-1}
--   \sqrt{\max\{R_\Omega,C_\Omega\}}\right)^q
--   $$
--   may be summed over $\Omega$ to obtain the corresponding Bernoulli-expectation bound.
--
--   Source: Candes-Recht 2008, Section 6.1, PDF pp. 24--25, the symmetrization/noncommutative-Khintchine calculation leading into Lemma 6.2/equation (6.6) and Theorem 6.3/equation (6.7).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
    (Ckh : ℝ) :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (∀ Omega : Finset (Fin n₁ × Fin n₂),
        rademacherExpectation
            (fun eps =>
              spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q) →
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
              Real.sqrt
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X))) ^ q) := by
  sorry
