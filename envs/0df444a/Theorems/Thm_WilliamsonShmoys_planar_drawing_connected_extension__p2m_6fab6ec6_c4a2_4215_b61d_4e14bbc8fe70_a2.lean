-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:10:09.013775+00:00
-- url     : https://prove2.me/theorems/e017d5db-f58c-45b7-b9c4-b8d059edab95
-- title:
--   Connected planar extension of a finite drawing with at least three vertices
-- statement:
--   Any finite graph on at least three vertices with a crossing-free drawing can be extended, on the same vertices, to a connected graph with a crossing-free drawing while retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ Q.Connected ∧
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel Q.Adj := dQ
         G.edgeFinset ⊆ Q.edgeFinset) := by sorry
