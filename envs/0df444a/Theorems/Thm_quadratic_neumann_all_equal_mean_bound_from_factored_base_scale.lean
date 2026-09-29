-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_mean_bound_from_factored_base_scale
-- name    : quadratic_neumann_all_equal_mean_bound_from_factored_base_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T09:06:58.03433+00:00
-- url     : https://prove2.me/theorems/84d476fd-68ec-4f3a-b517-8da468525e8f
-- statement:
--   This deterministic transfer lemma converts a base spectral-norm estimate into a bound for the all-equal mean contribution while retaining the exact scalar coefficient. If
--   $$Q_{mean}=p^{-2}(1-3p+2p^2),Q_{base},qquad
--   lVert Q_{base}Vertle C_{base}left(rac{mu_0r}{max(n_1,n_2)}ight)^2,$$
--   and the factored scalar quantity satisfies
--   $$C_{base}left|p^{-2}(1-3p+2p^2)ight|left(rac{mu_0r}{max(n_1,n_2)}ight)^2le C_{scale}lambda^{-3/2},$$
--   then
--   $$lVert Q_{mean}Vertle C_{scale}lambda^{-3/2}.$$
--   The proof is homogeneity of the spectral norm under scalar multiplication followed by the supplied factored scalar bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_mean_bound_from_factored_base_scale
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p Cbase Cscale lam μ₀ : ℝ) :
    quadraticNeumannAllEqualMeanContribution S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)) •
        quadraticNeumannAllEqualBaseMatrix S →
    spectralNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
      Cbase * ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
    Cbase *
        (|((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2))| *
          ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2)) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
  sorry
