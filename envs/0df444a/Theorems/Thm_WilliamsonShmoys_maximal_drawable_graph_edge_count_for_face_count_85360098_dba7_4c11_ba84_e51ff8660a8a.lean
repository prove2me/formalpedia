-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_for_face_count_85360098_dba7_4c11_ba84_e51ff8660a8a
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_count_85360098_dba7_4c11_ba84_e51ff8660a8a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:46:06.769402+00:00
-- url     : https://prove2.me/theorems/c9f2f72f-e500-46c8-ab0e-7bffe07c2b59
-- title:
--   Edge count of a maximal drawable graph for face counting
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_count_85360098_dba7_4c11_ba84_e51ff8660a8a
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T →
      R ≤ T → T = R)
    (hCard : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
