-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_exists_maximal_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
-- name    : WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_maximal_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:29:53.713983+00:00
-- url     : https://prove2.me/theorems/645517d8-cbfa-46dd-86f5-c3fab69b078b
-- title:
--   Existence of a maximal drawable supergraph for triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type is contained in an inclusion-maximal drawable simple graph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_supergraph_exists_maximal_aux_d3aee67b_a4ad_45fe_af2e_fefe3561f6fd
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    exists K : SimpleGraph V, H <= K /\ HasPlanarDrawingOn K /\
      forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K := by sorry
