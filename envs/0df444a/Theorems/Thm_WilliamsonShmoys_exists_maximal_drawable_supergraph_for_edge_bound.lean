-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_edge_bound
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:00:53.242853+00:00
-- url     : https://prove2.me/theorems/ae956985-6a48-4ca2-9b84-3169ccb4508c
-- title:
--   Finite maximal drawable supergraph extension for the edge bound
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal under adding edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet → K.edgeSet ≠ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
