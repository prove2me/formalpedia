-- Prove2me | Theorems.Thm_bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
-- name    : bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T19:51:18.905464+00:00
-- url     : https://prove2.me/theorems/0b961846-8c4e-4eb5-9594-c323aeff3268
-- statement:
--   Corrected finite-uniformization theorem for matrix-coordinate coefficient bounds, with the coordinate-cardinality loss explicit.
--
--   Assume $p\in[0,1]$. For every coordinate $w$ suppose
--   $$
--   \mathbb P_p\{|\operatorname{Coeff}_w(\Omega)|\le C_{\rm point}\,s\}
--   \ge 1-c_{\rm point}\eta.
--   $$
--   Then
--   $$
--   \mathbb P_p\{\forall w,\ |\operatorname{Coeff}_w(\Omega)|\le C_{\rm point}\,s\}
--   \ge 1-(n_1n_2)c_{\rm point}\eta.
--   $$
--
--   Unlike the older over-strong no-loss uniformization node, this statement keeps the finite-union factor $n_1n_2$ visible. Later Candes-Recht scalar estimates must absorb this loss by using a stronger pointwise exponent or an explicit beta shift.
--
--   Source context: standard finite union bound; this is the pointwise-to-uniform probability step used in the coefficient estimates in Candes-Recht 2008, Section 6.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∀ (p scale failureScale : ℝ), 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        ∀ Coeff : (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * failureScale) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w : Fin n₁ × Fin n₂,
                |Coeff w Omega| ≤ Cpoint * scale) ≥
          1 - (((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cpoint) *
            failureScale) := by
  sorry
