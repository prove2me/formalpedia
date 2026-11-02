-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph__p2m_3aaeb753_8214_46cb_ae23_34cf4eb39be4_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_3aaeb753_8214_46cb_ae23_34cf4eb39be4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:52:53.969383+00:00
-- url     : https://prove2.me/theorems/07094302-93b5-40e3-90fd-090a7e1ed5c9
-- title:
--   Complete a planar drawing to an edge-maximal planar graph
-- statement:
--   For every finite linearly ordered vertex type and planar drawing of a graph on at least three vertices, there is a planar supergraph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_3aaeb753_8214_46cb_ae23_34cf4eb39be4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel H.Adj := dH;
          H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
