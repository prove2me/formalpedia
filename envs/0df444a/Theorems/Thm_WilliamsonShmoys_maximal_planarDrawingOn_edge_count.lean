-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_count
-- name    : WilliamsonShmoys.maximal_planarDrawingOn_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:19:33.625431+00:00
-- url     : https://prove2.me/theorems/6426494a-70f3-49c7-bd08-e80ca3747577
-- title:
--   Edge count of a maximal connected planar graph
-- statement:
--   A connected planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex set has exactly 3n−6 edges. Prove this by showing maximality triangulates the embedding, then applying Euler’s formula and counting face-edge incidences; the vertex lower bound excludes the small exceptional cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planarDrawingOn_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v))
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
