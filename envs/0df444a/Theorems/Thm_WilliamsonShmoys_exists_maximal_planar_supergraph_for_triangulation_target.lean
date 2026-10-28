-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_triangulation_target
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_target
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:33:11.739167+00:00
-- url     : https://prove2.me/theorems/b20e0778-e58d-435d-9283-a1eb2bc2ab5d
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every graph with a drawing as defined by `HasPlanarDrawingOn` is contained in a planar supergraph on the same finite vertex type that is maximal among such supergraphs. Its edge count is at least the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_target
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) := by sorry
