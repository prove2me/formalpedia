-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planarOn_for_edge_count_extension
-- name    : WilliamsonShmoys.edge_count_of_maximal_planarOn_for_edge_count_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:02:16.942988+00:00
-- url     : https://prove2.me/theorems/25f0c05f-d0fa-4f04-8db8-d93667eb7ac7
-- title:
--   Edge count of a maximal planar drawing for edge-count extension
-- statement:
--   A planar graph on a finite ordered vertex type with at least three vertices, maximal under edge inclusion among planar graphs on that same vertex type, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planarOn_for_edge_count_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        J.edgeSet ⊆ K.edgeSet → K.edgeSet ⊆ J.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
