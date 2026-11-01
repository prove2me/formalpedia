-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximum_edge_supergraph__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
-- name    : WilliamsonShmoys.planar_drawing_maximum_edge_supergraph__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:20.781949+00:00
-- url     : https://prove2.me/theorems/78cb0e01-1105-4561-a4db-7810010c8df8
-- title:
--   A maximum-edge drawable supergraph exists
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices whose edge count is at least that of every drawable graph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximum_edge_supergraph__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ G ≤ Q ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        HasPlanarDrawingOn K →
        (letI : DecidableRel Q.Adj := dQ
         letI : DecidableRel K.Adj := dK
         Q.edgeFinset.card ≤ K.edgeFinset.card)) := by sorry
