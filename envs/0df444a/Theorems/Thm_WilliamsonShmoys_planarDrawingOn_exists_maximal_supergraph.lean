-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_supergraph
-- name    : WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:19:14.701173+00:00
-- url     : https://prove2.me/theorems/641e6fdf-f7b6-4ca2-a8be-de8f0d850ddf
-- title:
--   Maximal planar supergraph preserving connectivity
-- statement:
--   Extend the connected drawn graph, on the same vertices, to a planar graph maximal under adding edges, preserving connectivity and not decreasing the edge count. This can be proved by choosing a maximum planar supergraph from the finite set of possible edges and using the planar edge-addition argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
