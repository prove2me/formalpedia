-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_base_frobenius_norm_bound_min_dim
-- name    : quadratic_neumann_middle_index_distinct_centered_base_frobenius_norm_bound_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:37:40.125154+00:00
-- url     : https://prove2.me/theorems/a26d11b0-8083-4b94-b236-22eebbbe4d17
-- statement:
--   Per-entry FROBENIUS base bound (rectangular `min`-denominator) for the
--   MIDDLE-index centered coefficient of the quadratic Neumann term.
--
--   For output coordinate `w = (i,j)`, the fixed **two-kernel** base
--   `B^{(w)}_{ab} = if (a,b)=w then 0
--                  else signMatrix S w.1 w.2 · K(w.1,w.2,a,b) · K(a,b,w.1,w.2)`
--   has Frobenius norm bounded by
--   `Cfro·μ₁·√(r/(n₁n₂))·√(μ₀r/min)·(μ₀r/min)`.
--
--   The outer sign `signMatrix S w.1 w.2` is a constant over `(a,b)`; the two-kernel
--   product `K(ij,ab)·K(ab,ij)` replaces the first-index diagonal-kernel weight, and
--   carries the SAME tight `Φ`-scale (via `∑_{ab} K(ij,ab)² = K(ij,ij)` and the
--   pointwise off-diagonal kernel bound).
--
--   Source: Candès–Recht 2008, §6.3, PDF pp. 32–33, Lemma 6.7.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_base_frobenius_norm_bound_min_dim :
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
                  signMatrix S w.1 w.2 *
                    tangentCoordinateKernel S w.1 w.2 a b *
                      tangentCoordinateKernel S a b w.1 w.2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by sorry
