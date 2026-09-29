-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_centered_base_frobenius_norm_bound_min_dim
-- name    : quadratic_neumann_first_index_distinct_centered_base_frobenius_norm_bound_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T09:17:59.961672+00:00
-- url     : https://prove2.me/theorems/3d5e1c86-9bf4-4399-b33f-de56689a9129
-- statement:
--   Per-entry FROBENIUS base bound (rectangular `min`-denominator) for the
--   first-index centered coefficient of the quadratic Neumann term.
--
--   For output coordinate `w = (i,j)`, the fixed base
--   `B^{(w)}_{ab} = if (a,b)=w then 0 else (linearNeumannDiagonalBaseMatrix S a b)·K(a,b,w.1,w.2)`
--   has Frobenius norm bounded by
--   `Cfro·μ₁·√(r/(n₁n₂))·√(μ₀r/min)·(μ₀r/min)`.
--
--   The extra `(μ₀r/min)` factor relative to the off-diagonal base is the
--   diagonal-kernel weight `K(ab,ab)`.
--
--   Source: Candès–Recht 2008, §6.3, PDF pp. 31–32, Lemma 6.7 applied with
--   `X_ω = p^{-1} E_ω P_{ωω}`.
-- source:
--   Candès--Recht 2008, Exact Matrix Completion via Convex Optimization, PDF pp. 26 and 28--32, Theorem 6.3 (eq. 6.7), Lemma 6.6 (eqs. 6.15--6.17), Lemma 6.7 (eq. 6.19), and Section 6.3 around eqs. 6.20--6.21.

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Per-entry FROBENIUS base bound (rectangular `min`-denominator) for the
first-index centered coefficient of the quadratic Neumann term.

For output coordinate `w = (i,j)`, the fixed base
`B^{(w)}_{ab} = if (a,b)=w then 0 else (linearNeumannDiagonalBaseMatrix S a b)·K(a,b,w.1,w.2)`
has Frobenius norm bounded by
`Cfro·μ₁·√(r/(n₁n₂))·√(μ₀r/min)·(μ₀r/min)`.

The extra `(μ₀r/min)` factor relative to the off-diagonal base is the
diagonal-kernel weight `K(ab,ab)`.

Source: Candès–Recht 2008, §6.3, PDF pp. 31–32, Lemma 6.7 applied with
`X_ω = p^{-1} E_ω P_{ωω}`. -/
theorem quadratic_neumann_first_index_distinct_centered_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (fun a b =>
                if (a, b) = w then 0
                else
                  linearNeumannDiagonalBaseMatrix S a b *
                    tangentCoordinateKernel S a b w.1 w.2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by sorry
