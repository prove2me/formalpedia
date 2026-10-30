-- Prove2me | Theorems.Thm_WilliamsonShmoys_eq_of_subgraph_and_edge_card_le__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
-- name    : WilliamsonShmoys.eq_of_subgraph_and_edge_card_le__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:47.038701+00:00
-- url     : https://prove2.me/theorems/8c48e859-0738-4bbd-b42e-81868545339c
-- title:
--   Subgraph inclusion and edge cardinality rigidity
-- statement:
--   For finite simple graphs on the same vertex type, if G is a subgraph of H and H has no more edges than G, then the graphs are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.eq_of_subgraph_and_edge_card_le__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1 {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hGH : G ≤ H) (hcard : Nat.card {e : Sym2 V // e ∈ H.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ G.edgeSet}) : G = H := by sorry
