-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:00:58.481207+00:00
-- url     : https://prove2.me/theorems/9b84e475-7be1-4007-a2e0-d2e99948fc5d
-- title:
--   Edge bound for a planar subgraph of an edge-maximal planar graph
-- statement:
--   If a drawable graph is a subgraph of a graph maximal among drawable graphs on the same finite vertex type, then it has at most `3 * |V| - 6` edges when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hH : HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v))
    (hsub : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v)
    (dG : DecidableRel G.Adj)
    (dH : DecidableRel H.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG;
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
