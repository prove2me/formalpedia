-- Prove2me | Theorems.Thm_bernoulli_finite_index_intersection_probability_from_pointwise_bounds
-- name    : bernoulli_finite_index_intersection_probability_from_pointwise_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T20:02:13.683109+00:00
-- url     : https://prove2.me/theorems/0e42d6bc-341c-4e60-81ec-740770b0fb19
-- statement:
--   Finite-index Bernoulli union bound with the index-cardinality loss explicit.
--
--   Let $\iota$ be any finite index type. For each $i\in\iota$, let $E_i(\Omega)$ be an event in the Bernoulli observation model with parameter $p\in[0,1]$. If
--   $$
--   \mathbb P_p(E_i)\ge 1-c\eta\qquad\text{for every }i\in\iota,
--   $$
--   then
--   $$
--   \mathbb P_p\{\forall i\in\iota,\ E_i\}
--   \ge 1-|\iota|c\eta.
--   $$
--
--   This is the reusable finite-union-bound primitive for coordinate and pair-coordinate uniformization. The cardinality factor is deliberately visible; later scalar estimates must absorb it explicitly.
--
--   Source context: standard finite union bound, used throughout the coefficient-uniformization arguments in Candes-Recht 2008, Section 6.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
universe u

theorem bernoulli_finite_index_intersection_probability_from_pointwise_bounds
    {ι : Type u} [Fintype ι] [DecidableEq ι] {n₁ n₂ : ℕ}
    (p c failureScale : ℝ)
    (Event : ι → Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ i : ι, bernoulliEventProb p (Event i) ≥ 1 - c * failureScale) →
    bernoulliEventProb p (fun Omega => ∀ i : ι, Event i Omega) ≥
      1 - (((Fintype.card ι : ℝ) * c) * failureScale) := by
  sorry
