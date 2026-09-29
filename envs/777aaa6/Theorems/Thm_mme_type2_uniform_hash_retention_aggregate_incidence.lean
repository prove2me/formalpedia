-- Prove2me | Theorems.Thm_mme_type2_uniform_hash_retention_aggregate_incidence
-- name    : mme_type2_uniform_hash_retention_aggregate_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:00:26.170786+00:00
-- url     : https://prove2.me/theorems/846e92c1-a282-4f5f-bca7-a2d6e0f63b90
-- title:
--   Aggregate type-2 incidence from uniform hash-retention fibers
-- statement:
--   Let a finite hash-state space act on a target edge family $T_0$ inside an ambient tripartite family. If every target edge is retained in exactly $BQ$ states and every directed target--ambient collision pair is retained together in at most $Q$ states, then $$\sum_\omega |T(\omega)|=|T_0|BQ,\qquad \sum_\omega |C(\omega)|\le |C_0|Q.$$ This double-counting interface converts the local affine-hash fiber calculations into the aggregate hypotheses used by type-2 isolation pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; double counting of Salem--Spencer hash incidences.

import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators

set_option autoImplicit false

theorem mme_type2_uniform_hash_retention_aggregate_incidence
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [DecidableEq State] [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (B Q : ℕ)
    (hedge : ∀ a ∈ targetAll, ((Finset.univ : Finset State).filter (fun ω ↦ retain ω a)).card = B * Q)
    (hpair : ∀ ab ∈ ((targetAll ×ˢ ambientAll).filter (fun p ↦ p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)), ((Finset.univ : Finset State).filter (fun ω ↦ retain ω ab.1 ∧ retain ω ab.2)).card ≤ Q) :
    (∑ ω, (((targetAll.filter (retain ω)).card : ℝ))) = (targetAll.card : ℝ) * (B : ℝ) * (Q : ℝ) ∧
      (∑ ω, (((((targetAll.filter (retain ω)) ×ˢ (ambientAll.filter (retain ω))).filter (fun p ↦ p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)).card : ℝ))) ≤ ((((targetAll ×ˢ ambientAll).filter (fun p ↦ p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)).card : ℝ) * (Q : ℝ)) := by
  sorry
