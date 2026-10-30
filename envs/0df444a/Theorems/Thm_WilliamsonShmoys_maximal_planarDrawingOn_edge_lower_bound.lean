-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_planarDrawingOn_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:22:44.186981+00:00
-- url     : https://prove2.me/theorems/9d775f51-5705-4fa7-a5a7-f019b72b9ba6
-- title:
--   Maximal planar graph attains the triangulation lower bound
-- statement:
--   A connected planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has at least 3n−6 edges. A proof can extend its embedding to a triangulation on the same vertices, then use maximality to identify the extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planarDrawingOn_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v))
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by sorry
