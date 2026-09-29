-- Prove2me | Theorems.Thm_mme_tripartite_isolated_edge_pruning
-- name    : mme_tripartite_isolated_edge_pruning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:01:03.434864+00:00
-- url     : https://prove2.me/theorems/a83af475-7805-44ab-b327-52337af9737b
-- title:
--   Vertex-induced matching from an ordered collision budget
-- statement:
--   Let $E$ be a finite three-partite hypergraph and let $C$ be the set of ordered pairs of distinct edges sharing a vertex in at least one mode. There is a subset $F$ which is a matching and is vertex-induced relative to $E$: every edge of $E$ whose three vertices all occur among vertices of $F$ already belongs to $F$. Quantitatively,
--
--   $$
--   |E| ≤ |F|+|C|.
--   $$
--
--   This is a conservative deterministic form of the usual Coppersmith--Winograd collision deletion. With a modulus chosen so that ordered collisions consume less than a fixed fraction of the hashed target edges, it produces the full induced family needed for tensor zeroing; merely choosing a matching would not suffice.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), collision deletion on journal pp. 260--261 and its reuse on pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Finset.Prod

theorem mme_tripartite_isolated_edge_pruning
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (v : ∀ i, Edge → Vertex i) (E : Finset Edge) :
    let C := (E ×ˢ E).filter (fun p =>
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)
    ∃ F : Finset Edge,
      F ⊆ E ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y →
        ∀ i : Fin 3, v i x ≠ v i y) ∧
      (∀ e ∈ E,
        (∀ i : Fin 3, ∃ f ∈ F, v i e = v i f) → e ∈ F) ∧
      E.card ≤ F.card + C.card := by
  sorry
