-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximum_edge_planar_supergraph
-- name    : WilliamsonShmoys.exists_maximum_edge_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:13:44.806456+00:00
-- url     : https://prove2.me/theorems/34b1f723-a406-478b-ac4e-2af896ff5812
-- title:
--   Existence of a maximum-edge drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable supergraph on the same vertices whose edge count is at least that of every drawable supergraph containing it. Choose a maximum from the finite, nonempty family of such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximum_edge_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ N.edgeSet.ncard := by
  sorry
