-- Prove2me | Theorems.Thm_mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
-- name    : mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:50:27.164022+00:00
-- url     : https://prove2.me/theorems/b277d5a2-d287-44b7-a665-7735a9cb002e
-- title:
--   Type-2 hash loss budget from cardinality ratio and aggregate incidence
-- statement:
--   Let $T_0$ be a finite target-profile family inside an ambient tripartite family. Assume every ambient star through a target vertex has degree at most $D$. Across a finite hash-state space $\Omega$, suppose every target edge has total incidence $BQ$, every target--ambient collision pair has total incidence at most $Q$, $|\Omega|=PQ$, and $|T_0|=VD_*$. If $$P\ell+3D_*D\le D_*B,$$ then the aggregate retained-target mass exceeds the aggregate collision mass plus $|\Omega|V\ell$. This is precisely the averaged loss budget needed for ambient-isolation pruning, including the nontrivial same-marginal ratio occurring for $\varphi_{233}$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; aggregate Salem--Spencer hash incidence and collision budget.

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
    {State Edge : Type*} {Vertex : Fin 3 → Type*}
    [Fintype State] [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (ambientAll targetAll : Finset Edge)
    (ambient target : State → Finset Edge)
    (P B Q D Dstar : ℕ) (V loss : ℝ)
    (hV : 0 ≤ V)
    (hstate : Fintype.card State = P * Q)
    (htargetCard : (targetAll.card : ℝ) = V * (Dstar : ℝ))
    (hdegree : ∀ i : Fin 3, ∀ a ∈ targetAll, (ambientAll.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D)
    (htargetIncidence : ∑ ω, ((target ω).card : ℝ) = (targetAll.card : ℝ) * (B : ℝ) * (Q : ℝ))
    (hcollisionIncidence : ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦ p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)).card : ℝ) ≤ ((((targetAll ×ˢ ambientAll).filter (fun p ↦ p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)).card : ℝ) * (Q : ℝ)))
    (hmargin : (P : ℝ) * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤ (Dstar : ℝ) * (B : ℝ)) :
    (Fintype.card State : ℝ) * (V * loss) + ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦ p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)).card : ℝ) ≤ ∑ ω, ((target ω).card : ℝ) := by
  sorry
