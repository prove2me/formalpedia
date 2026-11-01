-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_47c18254_8e9b_4a76_b436_1915ac92f140_a1
-- name    : WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_47c18254_8e9b_4a76_b436_1915ac92f140_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:23:50.592546+00:00
-- url     : https://prove2.me/theorems/b5bac186-dc32-4d53-bbd2-ff87f7d5377f
-- title:
--   Drawable graphs extend to a triangulated graph with Euler edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set of size at least three has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_47c18254_8e9b_4a76_b436_1915ac92f140_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeFinset ⊆ H.edgeFinset ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
