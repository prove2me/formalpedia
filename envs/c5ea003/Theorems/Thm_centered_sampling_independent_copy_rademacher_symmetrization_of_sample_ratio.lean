-- Prove2me | Theorems.Thm_centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
-- name    : centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:11:08.38478+00:00
-- url     : https://prove2.me/theorems/9159bae0-3bdb-4a31-881e-ffc6fbf3771d
-- statement:
--   This is the sample-ratio-safe Rademacher symmetrization step for the independent-copy difference in Candes-Recht Section 6.1.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad S_\Omega(X)=p^{-1}(P_\Omega-pI)X.
--   $$
--   Assume $0<n_1$, $0<n_2$, $m\le n_1n_2$, and $q\ge1$. If $\Omega$ and $\Omega'$ are independent Bernoulli samples with inclusion probability $p$, then the symmetric difference $\delta_{ij}-\delta'_{ij}$ may be represented by an independent Rademacher sign. In the theorem interface this gives the moment comparison
--   $$
--   \mathbb E_{\Omega,\Omega'}\,\|S_\Omega(X)-S_{\Omega'}(X)\|^q
--   \le
--   \mathbb E_{\Omega,\Omega'}\mathbb E_\varepsilon\,\|S_{\Omega,\varepsilon}(X)-S_{\Omega',\varepsilon}(X)\|^q,
--   $$
--   where $S_{\Omega,\varepsilon}(X)=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_ie_j^\top$.
--
--   Source: Candes-Recht 2008, PDF p. 24, Section 6.1, immediately after equation (6.5), where the symmetry of $\delta_{ab}-\delta'_{ab}$ introduces the Rademacher sequence.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
      bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega Omega' =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                centeredSamplingFluctuation Omega'
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega Omega' =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                    rademacherSampledMatrix Omega' eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) := by
  sorry
