-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count_lower_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_lower_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:55:28.515376+00:00
-- url     : https://prove2.me/theorems/ab9a5ea2-18e4-4e60-89b6-dd4aa9d62bd2
-- title:
--   Lower bound from maximality of a planar drawing
-- statement:
--   A finite simple graph on at least three vertices that has the supplied crossing-free drawing and is maximal among planar supergraphs on that vertex set has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_lower_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall K : SimpleGraph V,
      M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
