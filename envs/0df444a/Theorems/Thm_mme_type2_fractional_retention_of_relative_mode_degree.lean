-- Prove2me | Theorems.Thm_mme_type2_fractional_retention_of_relative_mode_degree
-- name    : mme_type2_fractional_retention_of_relative_mode_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:30:49.034722+00:00
-- url     : https://prove2.me/theorems/d02ae350-a9f3-4b40-9bb1-17bfa846c43c
-- title:
--   Fractional type-2 retention from a relative mode-degree bound
-- statement:
--   Let a finite exact target family have cardinality $|T_0|=V D_*$, where $D_*$ is its reference mode degree. Suppose every target vertex has ambient degree at most $D$ and
--
--   $$
--   D\le \rho D_*.
--   $$
--
--   For a uniform type-2 hash with $PQ$ states, one-edge fiber $BQ$, and collision-pair fiber at most $Q$, assume retained supported triples have retained ambient completions. If the normalized margin
--
--   $$
--   P\ell+3\rho D_*\le B
--   $$
--
--   holds, then some state contains an induced, mode-disjoint retained family $F$ satisfying
--
--   $$
--   |F|\ge |T_0|\ell.
--   $$
--
--   This is the rate-preserving finite endpoint for the exceptional $\varphi_{233}$ argument. Once the same-marginal ambient degree is shown to exceed the exact degree by only a subexponential factor $\rho$, the theorem retains a subexponential fraction of the entire exact target rather than losing its exponential growth rate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Section 3.2, pp. 356--360, together with the exceptional same-marginal correction in Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib
import Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers

set_option autoImplicit false

theorem mme_type2_fractional_retention_of_relative_mode_degree
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (P B Q D Dstar : ℕ) (V rho ell : ℝ)
    (hV : 0 ≤ V)
    (hstate : Fintype.card State = P * Q)
    (htargetCard : (targetAll.card : ℝ) = V * (Dstar : ℝ))
    (hdegree : ∀ i : Fin 3, ∀ a ∈ targetAll,
      (ambientAll.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D)
    (hdegreeRatio : (D : ℝ) ≤ rho * (Dstar : ℝ))
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
      (P : ℝ) * ell + 3 * rho * (Dstar : ℝ) ≤ (B : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ targetAll.filter (retain ω) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      (targetAll.card : ℝ) * ell ≤ (kept.card : ℝ) := by
  sorry
