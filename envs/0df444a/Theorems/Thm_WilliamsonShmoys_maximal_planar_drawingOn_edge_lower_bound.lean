-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:15:51.466186+00:00
-- url     : https://prove2.me/theorems/db2981d6-4187-4329-933b-0bf8558e17ff
-- title:
--   Lower edge bound for a maximal graph with a planar drawing
-- statement:
--   A graph with a crossing-free drawing that is maximal among planar supergraphs on its fixed vertex set, and has at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
