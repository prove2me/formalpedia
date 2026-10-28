-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension_for_edge_count_extension
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension_for_edge_count_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:00:29.753855+00:00
-- url     : https://prove2.me/theorems/925b7128-d978-45b9-8efc-b6099450a21c
-- title:
--   Finite maximal planar extension for edge-count extension
-- statement:
--   A planar graph on a finite ordered vertex type has a planar supergraph on the same vertices that is maximal under edge inclusion among planar graphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension_for_edge_count_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      HasPlanarDrawingOn J ∧ G.edgeSet ⊆ J.edgeSet ∧
        ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
          J.edgeSet ⊆ K.edgeSet → K.edgeSet ⊆ J.edgeSet := by sorry
