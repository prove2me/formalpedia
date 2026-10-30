-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:49:44.867352+00:00
-- url     : https://prove2.me/theorems/2ad791f6-4940-481c-b7f0-90568050fed6
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph with a planar drawing that is inclusion-maximal among planar supergraphs on its vertex set, and has at least three vertices, has exactly `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
