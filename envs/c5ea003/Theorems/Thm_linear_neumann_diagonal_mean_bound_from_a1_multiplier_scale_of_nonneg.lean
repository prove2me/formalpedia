-- Prove2me | Theorems.Thm_linear_neumann_diagonal_mean_bound_from_a1_multiplier_scale_of_nonneg
-- name    : linear_neumann_diagonal_mean_bound_from_a1_multiplier_scale_of_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T16:01:31.451293+00:00
-- url     : https://prove2.me/theorems/88131d2e-fe92-4917-ad97-e3d8b6dbbf26
-- statement:
--   This formal bridge turns the A1-effective multiplier estimate and scalar absorption estimate into the deterministic diagonal mean bound.
--
--   If
--   $$
--   S_{0,\mathrm{mean}}=p^{-1}(1-p)D_T(E),
--   $$
--   if $0\le p\le1$, if $\|D_T(E)\|\le C\,{\mu_1^2r\over\min(n_1,n_2)}\|E\|$, and if $\|E\|\le1$, then the scalar inequality
--   $$
--   C\,p^{-1}(1-p){\mu_1^2r\over\min(n_1,n_2)}\le C'\lambda^{-1}
--   $$
--   implies
--   $$
--   \|S_{0,\mathrm{mean}}\|\le C'\lambda^{-1}.
--   $$
--
--   Source: This is a purely formal norm bridge for Candes-Recht 2008, PDF p. 26 equation (6.9), using Lemma 6.4 on PDF p. 27.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_mean_bound_from_a1_multiplier_scale_of_nonneg
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p Cdiag Cscale lam μ₁ : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 ≤ Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) →
    linearNeumannDiagonalMeanContribution S p =
      (p⁻¹ * (1 - p)) • tangentDiagonalMultiplier S (signMatrix S) →
    spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
      Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
        spectralNorm (signMatrix S) →
    spectralNorm (signMatrix S) ≤ 1 →
    Cdiag * ((p⁻¹ * (1 - p)) *
        (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂)))) ≤
      Cscale * Real.rpow lam (-1) →
    spectralNorm (linearNeumannDiagonalMeanContribution S p) ≤
      Cscale * Real.rpow lam (-1) := by
  sorry
