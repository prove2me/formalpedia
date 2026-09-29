-- Prove2me | Theorems.Thm_mme_type2_retained_cardinality_from_ambient_ratio
-- name    : mme_type2_retained_cardinality_from_ambient_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:27:04.491627+00:00
-- url     : https://prove2.me/theorems/f3405a62-4ec4-4fed-b412-18a8ac224d14
-- title:
--   Type-2 retained family from an ambient-to-target ratio
-- statement:
--   Let $T_0$ be a finite target family inside a finite ambient three-partite edge family $A$, and suppose $|A|\le \rho|T_0|$. A finite hash-state space has size $PQ$; every target edge is retained in exactly $BQ$ states; and every directed target--ambient collision pair is retained together in at most $Q$ states. Assume retained supported triples have retained ambient completions. If
--
--   $$
--   P\ell+3\rho|T_0|\le B,
--   $$
--
--   then some hash state contains an induced, mode-disjoint retained target family $F$ with
--
--   $$
--   |F|\ge |T_0|\ell.
--   $$
--
--   This ratio form is designed for the exceptional $\varphi_{233}$ constituent: an entropy argument bounds the larger same-marginal ambient family by a subexponential multiple of the exact-profile target, and that multiple can be inserted directly as $\rho$. No separate regularity or exact mode-degree calculation is required.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Section 3.2, pp. 356--360; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The ambient-ratio form packages the exceptional same-marginal correction in Lemma 5.1(v), pp. 365--367.

import Mathlib
import Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers

set_option autoImplicit false

theorem mme_type2_retained_cardinality_from_ambient_ratio
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (P B Q : ℕ) (rho loss : ℝ)
    (hstate : Fintype.card State = P * Q)
    (hambientRatio :
      (ambientAll.card : ℝ) ≤ rho * (targetAll.card : ℝ))
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
      (P : ℝ) * loss +
          3 * rho * (targetAll.card : ℝ) ≤ (B : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ targetAll.filter (retain ω) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      (targetAll.card : ℝ) * loss ≤ (kept.card : ℝ) := by
  sorry
