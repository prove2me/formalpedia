-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
-- name    : WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:39:17.321822+00:00
-- url     : https://prove2.me/theorems/fc016acd-24e0-4b4c-9f94-11715a39d633
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_edge_count_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
