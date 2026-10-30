-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:01.552852+00:00
-- url     : https://prove2.me/theorems/9423a00d-536e-4364-bafa-41e035674cb1
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on the fixed vertex type is contained in an inclusion-maximal drawable simple graph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

/-- Finite edge addition inside the class of drawable graphs yields an inclusion-maximal planar supergraph. -/

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : exists H : SimpleGraph V, G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\ forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H := by sorry
