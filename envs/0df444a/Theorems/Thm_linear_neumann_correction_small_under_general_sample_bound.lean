-- Prove2me | Theorems.Thm_linear_neumann_correction_small_under_general_sample_bound
-- name    : linear_neumann_correction_small_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:36:55.427146+00:00
-- url     : https://prove2.me/theorems/fd91a18d-66e9-4bc0-8976-4a0e63e18c54
-- statement:
--   First linear Neumann-correction estimate in the full Candès--Recht Theorem 1.3 sample regime.
--
--   Context and notation.  Let M be an n_1\times n_2 rank-r matrix with SVD data S.  Put n=\max(n_1,n_2) and p=m/(n_1n_2).  The Neumann-series dual certificate contains the first correction term
--   $$
--   L(\Omega)=p^{-1}P_{T^\perp}P_\Omega P_T H(E),
--   $$
--   where T is the tangent space at M, P_T and P_{T^\perp} are the tangent and normal projections, P_\Omega is Bernoulli entry sampling, and E=UV^\top is the sign matrix.
--
--   Mathematical claim.  There are universal constants C,c>0 such that, for every \beta>2, if M obeys the incoherence assumptions A0(S,\mu_0) and A1(S,\mu_1), and if
--   $$
--   m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\},nr,\beta\log n,\qquad C'\ge C,
--   $$
--   then
--   $$
--   \mathbb P_p\{\|L(\Omega)\|\le 1/8\}ge 1-c n^{-\beta}.
--   $$
--   This is the theorem-regime form of Candès--Recht Lemma 4.5 needed for the least-squares dual certificate.
--
--   Source and proof structure.  Source: Candès--Recht 2008, PDF p. 20, Lemma 4.5/equation (4.15), and PDF pp. 26--29, Section 6.2/equations (6.8)--(6.18).  The active source-correct sketch reduces this node to the diagonal contribution under the full sample bound, the off-diagonal contribution under the full sample bound, the deterministic diagonal/off-diagonal combination theorem, and the sample-ratio bound.  The diagonal branch follows equations (6.8)--(6.9), Theorem 6.3, and Lemma 6.4; the off-diagonal branch follows Lemma 6.5, equations (6.13)--(6.14), Lemma 6.6/equations (6.15)--(6.17), Theorem 6.3, and the decoupling transfer.  The previous lambda-only sketch route has been deprecated because it relied on the stale standalone diagonal-centered path rather than the corrected rectangular min-dimensional Section 6.2 route.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_correction_small_under_general_sample_bound :
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
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 1 ((1 : ℝ) / 8)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
