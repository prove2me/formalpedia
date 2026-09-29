-- Prove2me | Theorems.Thm_mme_target_ambient_three_mode_collision_card_le_of_fiber_degree
-- name    : mme_target_ambient_three_mode_collision_card_le_of_fiber_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:44:58.013422+00:00
-- url     : https://prove2.me/theorems/4afdc4da-987a-4b92-a9a3-83ed36253d7c
-- title:
--   Three-mode target--ambient collision bound from uniform degree
-- statement:
--   Let $T$ be a finite target family in a finite ambient tripartite edge family $A$. If every ambient star through every target vertex, in each of the three modes, has cardinality at most $D$, then the number of directed pairs $(a,b)\in T\times A$ with $a\ne b$ that share at least one mode vertex is at most $$3|T|D.$$ The ambient second component is essential when a marginal fiber contains several joint profiles, as for the Davie--Stothers $\varphi_{233}$ constituent.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356-360; union bound for target-to-ambient vertex collisions.

import Mathlib

set_option autoImplicit false

theorem mme_target_ambient_three_mode_collision_card_le_of_fiber_degree
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (ambient target : Finset Edge)
    (vertex : ∀ i, Edge → Vertex i) (D : ℕ)
    (hdeg : ∀ i : Fin 3, ∀ a ∈ target,
      (ambient.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D) :
    (((target ×ˢ ambient).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)).card) ≤
      3 * target.card * D := by
  sorry
