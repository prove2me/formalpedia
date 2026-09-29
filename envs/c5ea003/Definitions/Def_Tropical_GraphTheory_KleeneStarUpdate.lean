-- Prove2me | Definitions.Def_Tropical_GraphTheory_KleeneStarUpdate
-- name    : Tropical_GraphTheory_KleeneStarUpdate
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:18.528483+00:00
-- url     : https://prove2.me/theorems/e56eb948-4505-4539-b5c2-6d69c4e174a9
-- title:
--   Aether Catalog definitions — Tropical_GraphTheory_KleeneStarUpdate
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.GraphTheory.KleeneStarUpdate`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/GraphTheory/KleeneStarUpdate.lean by skeleton subtraction
import Mathlib

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

namespace TropicalAPSP

/-! ## APSP Closure Definition -/

/-- `IsAPSPClosure A S` asserts that `S` is the **least reflexive-transitive closure**
of adjacency matrix `A` in the min-plus (tropical) semiring over `ENNReal`.

Concretely, `S` satisfies:
1. `S ≤ A` entrywise (direct edges are valid paths),
2. `S(i,i) = 0` (reflexivity: zero-cost identity path),
3. `S(i,j) ≤ S(i,k) + S(k,j)` for all `k` (transitivity: path concatenation),
4. `S` is pointwise minimal among all matrices satisfying (1)–(3). -/
structure IsAPSPClosure {n : ℕ} (A S : Matrix (Fin n) (Fin n) ENNReal) : Prop where
  le_adj : ∀ i j, S i j ≤ A i j
  diag_eq : ∀ i, S i i = 0
  triangle : ∀ i j k, S i j ≤ S i k + S k j
  minimal : ∀ T : Matrix (Fin n) (Fin n) ENNReal,
    (∀ i j, T i j ≤ A i j) →
    (∀ i, T i i = 0) →
    (∀ i j k, T i j ≤ T i k + T k j) →
    ∀ i j, S i j ≤ T i j

/-! ## Edge Update Definition -/

/-- Single-edge update: modify the adjacency matrix by adding an edge `u → v`
with weight `w`, taking the minimum with the existing weight. -/
def edgeUpdate {n : ℕ} (A : Matrix (Fin n) (Fin n) ENNReal)
    (u v : Fin n) (w : ENNReal) : Matrix (Fin n) (Fin n) ENNReal :=
  fun i j => min (A i j) (if i = u ∧ j = v then w else ⊤)





/-! ## Key Algebraic Helper Lemma -/

/-
If `P ≤ a + c`, `Q ≤ a + d`, `Q ≤ b + c`, and `Q ≤ b + d`,
then `min P Q ≤ min a b + min c d`.

This is a general algebraic fact for `ENNReal` that captures the core
of the tropical triangle inequality under surgery.
-/

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

end TropicalAPSP


