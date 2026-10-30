-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_for_face_equations_e86e41b9
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_equations_e86e41b9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:25:47.822371+00:00
-- url     : https://prove2.me/theorems/ed94ab16-2350-4c99-9081-83555002224e
-- title:
--   Edge count of a maximal drawable graph for face equations
-- statement:
--   A vertex-maximal graph with a crossing-free drawing and at least three vertices has exactly $3n-6$ edges. This child contains the planar-topological work; the parent uses the resulting edge equation to construct the requested face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_equations_e86e41b9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
