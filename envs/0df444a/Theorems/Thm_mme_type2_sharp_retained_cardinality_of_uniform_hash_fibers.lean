-- Prove2me | Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
-- name    : mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:16:42.157722+00:00
-- url     : https://prove2.me/theorems/6e152c32-eb1b-4c6f-bcf3-a14b897c0adf
-- title:
--   Sharp retained-family bound from uniform type-2 hash fibers
-- statement:
--   Let $T_0$ be a finite target family inside an ambient tripartite edge family, and let a finite state space act through a retention predicate. Suppose every target edge is retained in exactly $BQ$ states and every directed target--ambient collision pair is retained together in at most $Q$ states. Assume every target vertex has ambient degree at most $D$, the state-space size is $PQ$, and
--
--   $$
--   |T_0|=V D_*,\qquad P\ell+3D_*D\le D_*B.
--   $$
--
--   If target edges lie in the ambient family and every supported triple of retained targets has a retained ambient completion, then some state contains an induced, mode-disjoint retained target family $F$ satisfying
--
--   $$
--   |F|\ge V\ell.
--   $$
--
--   This is the sharp finite cardinality endpoint of the type-2 hashing argument. It combines uniform one-edge and pair fibers, the three-mode degree union bound, averaging, and deterministic isolation, while leaving the concrete edge alphabet and hash construction as parameters. In particular, the affine pair estimate for a specific profile can be plugged into the `hpair` hypothesis without changing the pruning proof.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, proof of Lemma 3.3 and the type-2 construction in Section 3.2, printed pp. 356--360; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib
import Theorems.Thm_mme_type2_uniform_hash_retention_aggregate_incidence
import Theorems.Thm_mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
import Theorems.Thm_mme_type2_induced_family_of_hash_collision_budget

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (P B Q D Dstar : ℕ) (V loss : ℝ)
    (hV : 0 ≤ V)
    (hstate : Fintype.card State = P * Q)
    (htargetCard : (targetAll.card : ℝ) = V * (Dstar : ℝ))
    (hdegree : ∀ i : Fin 3, ∀ a ∈ targetAll,
      (ambientAll.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D)
    (hedge : ∀ a ∈ targetAll,
      ((Finset.univ : Finset State).filter
        (fun ω ↦ retain ω a)).card = B * Q)
    (hpair : ∀ ab ∈ ((targetAll ×ˢ ambientAll).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)),
      ((Finset.univ : Finset State).filter
        (fun ω ↦ retain ω ab.1 ∧ retain ω ab.2)).card ≤ Q)
    (htargetAmbient : targetAll ⊆ ambientAll)
    (hclosure : ∀ ω,
      ∀ x ∈ targetAll.filter (retain ω),
      ∀ y ∈ targetAll.filter (retain ω),
      ∀ z ∈ targetAll.filter (retain ω),
        supportedMix x y z →
          ∃ e ∈ ambientAll.filter (retain ω),
            vertex 0 e = vertex 0 x ∧
            vertex 1 e = vertex 1 y ∧
            vertex 2 e = vertex 2 z)
    (hmargin :
      (P : ℝ) * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (B : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ targetAll.filter (retain ω) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      V * loss ≤ (kept.card : ℝ) := by
  sorry
