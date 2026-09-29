-- Prove2me | solution 1 for TropicalAPSP.edgeUpdate_closure_triangle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:24.301627+00:00
-- url     : https://prove2.me/submissions/d64f19fb-c9c6-462d-9208-14e32c1423a4

-- Sol generated from Tropical/GraphTheory/KleeneStarUpdate.lean
import Mathlib
import Definitions.Def_Tropical_GraphTheory_KleeneStarUpdate

/-!
# Kleene Star Single-Edge Update for Tropical APSP Closure

This file proves the tropical analogue of the Sherman–Morrison formula for
all-pairs shortest paths (APSP). When a single edge `u → v` of weight `w` is
added to a weighted directed graph with nonnegative edge weights (modeled in
`ENNReal`), the APSP closure matrix updates via an exact rank-one tropical formula:

  `S'(i,j) = min( S(i,j), S(i,u) + w + S(v,j) )`

where `S` is the original APSP closure and `S'` is the new one.

## Main Definitions

* `TropicalAPSP.IsAPSPClosure A S` — `S` is the least reflexive-transitive closure
  of adjacency matrix `A` in the min-plus semiring.
* `TropicalAPSP.edgeUpdate A u v w` — modify `A` by adding edge `u → v` with weight `w`.

## Main Results

* `TropicalAPSP.kleene_star_single_edge_update` — the APSP closure of `edgeUpdate A u v w`
  is exactly `fun i j ↦ min (S i j) (S i u + w + S v j)`.
* `TropicalAPSP.apsp_edge_update_mono` — edge insertion can only decrease shortest-path costs.
* `TropicalAPSP.apsp_closure_unique` — the APSP closure is unique.

## References

This is the tropical (min-plus) analogue of the Sherman–Morrison rank-one matrix
inverse update. It is foundational for certified dynamic shortest-path algorithms
and tropical perturbation theory.
-/

open Matrix

noncomputable section

open TropicalAPSP

/-! ## APSP Closure Definition -/


/-! ## Edge Update Definition -/






/-! ## Key Algebraic Helper Lemma -/

/-
If `P ≤ a + c`, `Q ≤ a + d`, `Q ≤ b + c`, and `Q ≤ b + d`,
then `min P Q ≤ min a b + min c d`.

This is a general algebraic fact for `ENNReal` that captures the core
of the tropical triangle inequality under surgery.
-/
lemma min_le_min_add_min {P Q a b c d : ENNReal}
    (h1 : P ≤ a + c) (h2 : Q ≤ a + d) (h3 : Q ≤ b + c) (h4 : Q ≤ b + d) :
    min P Q ≤ min a b + min c d := by
  cases le_total a b <;> cases le_total c d <;> simp +decide [*]

/-! ## Proof Components for the Main Theorem -/

/-
**Condition 1**: The updated closure is below the updated adjacency matrix.
-/

/-
**Condition 2**: The diagonal of the updated closure is zero.
-/

/-
**Condition 3**: The updated closure satisfies the triangle inequality.

This is the key technical step. For any intermediate vertex `k`, we need
  `min(S(i,j), S(i,u)+w+S(v,j)) ≤ min(S(i,k), S(i,u)+w+S(v,k)) + min(S(k,j), S(k,u)+w+S(v,j))`

The proof uses `min_le_min_add_min` with four bounds derived from the
triangle inequality of the original closure `S`.
-/

/-
**Condition 4**: The updated closure is minimal.

Given any matrix `T` satisfying the closure conditions for the updated graph,
we show `S' ≤ T` entrywise. The key insight: since `edgeUpdate A u v w ≤ A`
entrywise, `T` also satisfies the closure conditions for `A`. By minimality
of `S` for `A`, we get `S ≤ T`, hence `min(S, ...) ≤ S ≤ T`.
-/

/-! ## Main Theorem -/


/-! ## Corollaries -/


/-
**Monotonicity**: Adding an edge can only decrease shortest-path costs.
-/

/-
**Idempotence**: Applying the same edge update twice yields the same closure.
-/


open TropicalAPSP in
theorem solution{n : ℕ}
    {A S : Matrix (Fin n) (Fin n) ENNReal}
    (hS : IsAPSPClosure A S)
    (u v : Fin n) (w : ENNReal) :
    ∀ i j k, min (S i j) (S i u + w + S v j) ≤
      min (S i k) (S i u + w + S v k) + min (S k j) (S k u + w + S v j) := by
  -- By the properties of min, we can split the inequality into two parts.
  intro i j k
  apply min_le_min_add_min;
  · exact hS.triangle i j k;
  · convert add_le_add_right ( hS.triangle i u k ) ( w + S v j ) using 1 ; ring;
    abel1;
  · convert add_le_add_left ( hS.triangle v j k ) ( S i u + w ) using 1 ; ring;
    abel1;
  · simp +decide [ add_assoc ];
    gcongr;
    refine' le_trans _ ( le_add_of_nonneg_left <| zero_le );
    exact le_add_of_nonneg_of_le ( zero_le ) ( le_add_of_nonneg_left ( zero_le ) )
