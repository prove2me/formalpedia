-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_maximal_supergraph
-- name    : WilliamsonShmoys.planar_simple_edge_bound_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:56:10.213058+00:00
-- url     : https://prove2.me/theorems/e577d17b-a08b-4642-9c0c-08f465bf14a6
-- title:
--   Maximal drawn supergraph on the same vertices
-- statement:
--   Extend G to an inclusion-maximal graph on V that still admits the specified drawing. Since V is finite, there are finitely many simple graphs on V; maximizing edge count among drawn supergraphs gives a maximal extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_bound_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  sorry
