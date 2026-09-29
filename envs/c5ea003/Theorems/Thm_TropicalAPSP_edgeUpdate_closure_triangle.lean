-- Prove2me | Theorems.Thm_TropicalAPSP_edgeUpdate_closure_triangle
-- name    : TropicalAPSP.edgeUpdate_closure_triangle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:49.08422+00:00
-- url     : https://prove2.me/theorems/983746d9-6522-4e77-9962-f8a0e6eb67a7
-- title:
--   EdgeUpdate closure triangle
-- statement:
--   Formal statement of `TropicalAPSP.edgeUpdate_closure_triangle` from the Aether Catalog (Tropical). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalAPSP.edgeUpdate_closure_triangle{n : ℕ}
--       {A S : Matrix (Fin n) (Fin n) ENNReal}
--       (hS : IsAPSPClosure A S)
--       (u v : Fin n) (w : ENNReal) :
--       ∀ i j k, min (S i j) (S i u + w + S v j) ≤
--         min (S i k) (S i u + w + S v k) + min (S k j) (S k u + w + S v j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/GraphTheory/KleeneStarUpdate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/GraphTheory/KleeneStarUpdate.lean#L138

-- Thm stub generated from Tropical/GraphTheory/KleeneStarUpdate.lean
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

theorem TropicalAPSP.edgeUpdate_closure_triangle{n : ℕ}
    {A S : Matrix (Fin n) (Fin n) ENNReal}
    (hS : IsAPSPClosure A S)
    (u v : Fin n) (w : ENNReal) :
    ∀ i j k, min (S i j) (S i u + w + S v j) ≤
      min (S i k) (S i u + w + S v k) + min (S k j) (S k u + w + S v j) := by sorry
