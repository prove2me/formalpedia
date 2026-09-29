-- Prove2me | Theorems.Thm_mme_tripartite_target_isolation_pruning
-- name    : mme_tripartite_target_isolation_pruning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:03:49.255501+00:00
-- url     : https://prove2.me/theorems/9d923c69-b635-4817-bba0-03da2198f220
-- title:
--   Induced target matching from directed ambient collisions
-- statement:
--   Let $T$ be a finite target subfamily of a three-partite hypergraph $E$. Let $C$ consist of ordered pairs $(t,e)$ with $t$ a target edge, $e$ an ambient edge, $t ≠ e$, and the two edges sharing a vertex. There is a target subfamily $F$ which is a matching and is vertex-induced relative to the whole ambient hypergraph, with
--
--   $$
--   |T| ≤ |F|+|C|.
--   $$
--
--   The direction of the collision set is important for the Coppersmith--Winograd outer hash. It is enough to count collisions incident to the dominant equation-(13) target edges, while the ambient edge set still contains every supported mixed triple with the prescribed marginals. Thus the conclusion proves full inducedness without paying for irrelevant collisions between two non-target edges.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), collision deletion on journal pp. 260--261 and dominant-profile reuse on pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Finset.Prod

theorem mme_tripartite_target_isolation_pruning
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (v : ∀ i, Edge → Vertex i) (E T : Finset Edge) (hTE : T ⊆ E) :
    let C := (T ×ˢ E).filter (fun p =>
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)
    ∃ F : Finset Edge,
      F ⊆ T ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y →
        ∀ i : Fin 3, v i x ≠ v i y) ∧
      (∀ e ∈ E,
        (∀ i : Fin 3, ∃ f ∈ F, v i e = v i f) → e ∈ F) ∧
      T.card ≤ F.card + C.card := by
  sorry
