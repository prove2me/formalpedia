-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_edge_count_completion_64e86cee
-- name    : WilliamsonShmoys.planar_drawing_supergraph_edge_count_completion_64e86cee
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:06:54.376489+00:00
-- url     : https://prove2.me/theorems/98108dba-1927-4e81-b6e3-ce95ad278038
-- title:
--   Planar drawing completion with exact edge count
-- statement:
--   For every drawable finite simple graph on at least three vertices, there is a drawable supergraph on the same vertices with exactly \(3|V|-6\) edges. This is the triangulation-completion step: connect components and add noncrossing edges until the embedding is triangulated, then use Euler’s formula. The three-vertex boundary case is included; the cardinality hypothesis is needed for the stated planar triangulation count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_edge_count_completion_64e86cee
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
