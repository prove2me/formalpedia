-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:30:20.981302+00:00
-- url     : https://prove2.me/theorems/b2facf4f-375b-4f83-ba19-34094f723a5d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V,
      M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
