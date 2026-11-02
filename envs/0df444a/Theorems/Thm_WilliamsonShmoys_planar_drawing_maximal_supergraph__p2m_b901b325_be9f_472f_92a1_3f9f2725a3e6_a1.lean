-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:02:15.978388+00:00
-- url     : https://prove2.me/theorems/23f134b1-374c-4250-9a94-0278c2487544
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
