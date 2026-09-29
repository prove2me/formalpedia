-- Prove2me | Theorems.Thm_mme_type2_marginally_closed_target_pruning
-- name    : mme_type2_marginally_closed_target_pruning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:17:40.02387+00:00
-- url     : https://prove2.me/theorems/e31fed4b-4c75-4a16-bef1-f0cfb45f83db
-- title:
--   Collision-budget pruning for marginally closed type-2 profiles
-- statement:
--   Let $S_0$ be a finite target profile inside an ambient same-marginal edge family. Every edge has one vertex in each of three arbitrary finite-mode alphabets. Assume that every supported mixture of three target edges has an ambient completion with the selected vertices, and that the target profile is closed under any ambient completion whose three vertices are represented in the target. Define $C$ to be the set of ordered pairs of distinct target edges sharing at least one mode vertex. Then there is a retained family $F\subseteq S_0$ such that all three vertex maps are injective on $F$, every supported mixed triple in $F$ is diagonal, and $$|S_0|\le |F|+|C|.$$ This is the exact collision-budget form of the deterministic pruning step in the type-2 Salem--Spencer argument. Marginal determinacy supplies the closure assumption for the $116$, $125$, $134$, and $224$ constituent profiles; the $233$ profile instead needs its nontrivial same-marginal correction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Section 3.2, printed pp. 356-360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Theorems.Thm_mme_tripartite_target_isolation_pruning

set_option autoImplicit false

theorem mme_type2_marginally_closed_target_pruning
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambient target : Finset Edge)
    (hclosure : ∀ x ∈ target, ∀ y ∈ target, ∀ z ∈ target,
      supportedMix x y z →
        ∃ e ∈ ambient,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z)
    (hprofile : ∀ e ∈ ambient,
      (∀ i : Fin 3, ∃ f ∈ target, vertex i e = vertex i f) →
        e ∈ target) :
    let collisions := (target ×ˢ target).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)
    ∃ kept : Finset Edge,
      kept ⊆ target ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      target.card ≤ kept.card + collisions.card := by
  sorry
