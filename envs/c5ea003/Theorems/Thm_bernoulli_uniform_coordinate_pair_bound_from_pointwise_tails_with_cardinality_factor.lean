-- Prove2me | Theorems.Thm_bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
-- name    : bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T20:04:33.494922+00:00
-- url     : https://prove2.me/theorems/6192742b-f44a-46da-b11b-eb335eaf3413
-- statement:
--   Corrected finite-uniformization over ordered pairs of matrix coordinates, with the pair-cardinality loss explicit.
--
--   Assume $p\in[0,1]$. For every ordered pair of matrix coordinates $(w_1,w_2)$, suppose
--   $$
--   \mathbb P_p\{|\operatorname{Coeff}_{w_1,w_2}(\Omega)|\le C_{\rm point}s\}
--   \ge 1-c_{\rm point}\eta.
--   $$
--   Then the simultaneous pair-coordinate bound satisfies
--   $$
--   \mathbb P_p\{\forall w_1,w_2,\ |\operatorname{Coeff}_{w_1,w_2}(\Omega)|\le C_{\rm point}s\}
--   \ge
--   1-|\{(w_1,w_2)\}|c_{\rm point}\eta.
--   $$
--
--   This corrects the over-strong no-loss pair-uniformization pattern by retaining the finite union-bound factor. Later scalar estimates must absorb this factor explicitly, usually by starting with stronger pointwise tails.
--
--   Source context: standard finite union bound used in the all-distinct coefficient estimates in Candes-Recht 2008, Section 6.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∀ (p scale failureScale : ℝ), 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        ∀ Coeff : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * failureScale) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w1 w2 : Fin n₁ × Fin n₂,
                |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
          1 -
            (((Fintype.card
              ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) *
              cpoint) * failureScale) := by
  sorry
