-- Prove2me | Theorems.Thm_linear_neumann_diagonal_mean_bound_from_multiplier_scale_of_nonneg
-- name    : linear_neumann_diagonal_mean_bound_from_multiplier_scale_of_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T07:43:50.900051+00:00
-- url     : https://prove2.me/theorems/af0f25ee-95d6-400d-8b65-c17ca1a95d76
-- statement:
--   Role. This corrected deterministic leaf repairs the diagonal-mean transfer in the linear Neumann correction branch of the Candes-Recht golfing certificate.
--
--   Problem and notation. In the Bernoulli matrix-completion model, let (p) be the sampling probability and let (S) encode the singular-vector data of the rank-(r) matrix. The matrix
--   (operatorname{linearNeumannDiagonalMeanContribution}(S,p)) is the deterministic mean part of the diagonal first-order Neumann term. The operator (operatorname{tangentDiagonalMultiplier}_S) multiplies the sign matrix by the diagonal tangent-kernel weights.
--
--   Claim. Assume (0le ple1), the mean contribution is represented as
--
--   $$
--   operatorname{linearNeumannDiagonalMeanContribution}(S,p)
--   = p^{-1}(1-p),operatorname{tangentDiagonalMultiplier}_S(operatorname{signMatrix}(S)),
--   $$
--
--   and the tangent diagonal multiplier satisfies
--
--   $$
--   |operatorname{tangentDiagonalMultiplier}_S(operatorname{signMatrix}(S))|
--   le
--   C_{mathrm{diag}}rac{mu_0 r}{max(n_1,n_2)},|operatorname{signMatrix}(S)|.
--   $$
--
--   If the deterministic scale (C_{mathrm{diag}}mu_0 r/max(n_1,n_2)) is nonnegative, (|operatorname{signMatrix}(S)|le1), and the scalar estimate
--
--   $$
--   C_{mathrm{diag}},p^{-1}(1-p)rac{mu_0 r}{max(n_1,n_2)}
--   le C_{mathrm{scale}}lambda^{-1}
--   $$
--
--   holds, then
--
--   $$
--   |operatorname{linearNeumannDiagonalMeanContribution}(S,p)|
--   le C_{mathrm{scale}}lambda^{-1}.
--   $$
--
--   The added nonnegativity hypothesis is the necessary condition for multiplying the sign-matrix norm bound by the deterministic scale; it is available in the intended parent theorem from positive constants and positive dimensions.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Deterministic transfer from Lemma 6.4 and the scalar sample-size estimate
to the diagonal mean contribution bound, with the nonnegativity condition
needed to multiply by the sign-matrix spectral bound. -/

theorem linear_neumann_diagonal_mean_bound_from_multiplier_scale_of_nonneg
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p Cdiag Cscale lam μ₀ : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 ≤ Cdiag * (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) →
    linearNeumannDiagonalMeanContribution S p =
      (p⁻¹ * (1 - p)) • tangentDiagonalMultiplier S (signMatrix S) →
    spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
      Cdiag * (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) *
        spectralNorm (signMatrix S) →
    spectralNorm (signMatrix S) ≤ 1 →
    Cdiag * ((p⁻¹ * (1 - p)) *
        (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) ≤
      Cscale * Real.rpow lam (-1) →
    spectralNorm (linearNeumannDiagonalMeanContribution S p) ≤
      Cscale * Real.rpow lam (-1) := by
  sorry
