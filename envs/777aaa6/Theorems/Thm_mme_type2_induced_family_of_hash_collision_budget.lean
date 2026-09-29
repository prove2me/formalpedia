-- Prove2me | Theorems.Thm_mme_type2_induced_family_of_hash_collision_budget
-- name    : mme_type2_induced_family_of_hash_collision_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:27:12.740255+00:00
-- url     : https://prove2.me/theorems/1ce808e5-445c-4fab-bb1e-3e84fed87c45
-- title:
--   Type-2 induced family from a finite hash collision budget
-- statement:
--   Let $\Omega$ be any nonempty finite family of hash states. At state $\omega$, let $S_0(\omega)$ be a retained target-profile edge set inside a retained ambient same-marginal family $S(\omega)$. Every edge has one vertex in each of three arbitrary mode alphabets, and every supported mixture of three target edges admits a completion in the ambient family. If a real number $L$ satisfies the global incidence budget $$|\Omega|L+\sum_{\omega\in\Omega} C(\omega)\le \sum_{\omega\in\Omega}|S_0(\omega)|,$$ where $C(\omega)$ counts ordered pairs consisting of one target edge and one distinct ambient edge that share a mode vertex, then some state contains an induced, mode-disjoint target family $F$ with $|F|\ge L$. This is the reusable averaging-and-pruning endpoint of the type-2 Salem--Spencer construction. It covers trivial marginal fibers directly and accommodates the $233$ profile once its target-to-ambient product estimate is supplied in the collision budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, proof of Lemma 3.3 and the type-2 construction in Section 3.2, printed pp. 356-360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Theorems.Thm_mme_finite_collision_budget_averaging_real
import Theorems.Thm_mme_tripartite_target_isolation_pruning

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_type2_induced_family_of_hash_collision_budget
    {State : Type} {Edge : Type*} {Vertex : Fin 3 → Type*}
    [Fintype State] [Nonempty State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambient target : State → Finset Edge)
    (htarget : ∀ ω, target ω ⊆ ambient ω)
    (hclosure : ∀ ω, ∀ x ∈ target ω, ∀ y ∈ target ω,
      ∀ z ∈ target ω, supportedMix x y z →
        ∃ e ∈ ambient ω,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z)
    (loss : ℝ)
    (hbudget :
      (Fintype.card State : ℝ) * loss +
          ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card : ℝ) ≤
        ∑ ω, ((target ω).card : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ target ω ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      loss ≤ (kept.card : ℝ) := by
  sorry
