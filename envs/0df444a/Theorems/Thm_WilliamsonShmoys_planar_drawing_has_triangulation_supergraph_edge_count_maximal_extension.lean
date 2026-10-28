-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph_edge_count_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:47:22.840911+00:00
-- url     : https://prove2.me/theorems/dfc8dd7b-750b-4c77-a37e-c5d8c0e00115
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertex type. This is obtained by maximizing edge count over the finite family of candidate supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists M : SimpleGraph V, N <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) := by sorry
