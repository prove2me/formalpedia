-- Prove2me | Theorems.Thm_bernoulli_finite_coordinate_intersection_probability_from_pointwise_bounds
-- name    : bernoulli_finite_coordinate_intersection_probability_from_pointwise_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T19:47:05.690731+00:00
-- url     : https://prove2.me/theorems/76e62122-1a31-44c3-a2c7-13989905597e
-- statement:
--   Finite-coordinate Bernoulli union bound with the coordinate-cardinality loss made explicit.
--
--   Let $\Omega$ be drawn from the Bernoulli observation model with parameter $p\in[0,1]$ on the $n_1n_2$ matrix coordinates. For each coordinate
--   $$
--   w\in \{1,\dots,n_1\}\times\{1,\dots,n_2\},
--   $$
--   let $E_w(\Omega)$ be an event. If each coordinate event satisfies
--   $$
--   \mathbb P_p(E_w)\ge 1-c\,\eta,
--   $$
--   then the simultaneous event satisfies
--   $$
--   \mathbb P_p\bigl(\forall w,\ E_w\bigr)
--   \ge
--   1-(n_1n_2)c\,\eta.
--   $$
--
--   This theorem deliberately keeps the factor $n_1n_2$ visible. It is the honest finite-union bound needed before later scalar lemmas absorb this cardinality loss into stronger pointwise polynomial tails.
--
--   Source context: standard finite union bound; this is the probability step used in the coefficient uniformization arguments around Candes-Recht 2008, Section 6.1 and the later Section 6 coefficient estimates where pointwise tail bounds are upgraded to uniform coordinate events.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_finite_coordinate_intersection_probability_from_pointwise_bounds
    {n₁ n₂ : ℕ} (p c failureScale : ℝ)
    (Event : (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ w : Fin n₁ × Fin n₂,
      bernoulliEventProb p (Event w) ≥ 1 - c * failureScale) →
    bernoulliEventProb p (fun Omega => ∀ w : Fin n₁ × Fin n₂, Event w Omega) ≥
      1 - (((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * c) * failureScale) := by
  sorry
