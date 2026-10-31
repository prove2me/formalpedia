-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:48.433821+00:00
-- url     : https://prove2.me/theorems/9bc7c850-285b-4c6d-a405-b91e421d93f9
-- title:
--   Connected planar extension of a finite drawing
-- statement:
--   Any finite graph with a crossing-free drawing can be extended, on the same vertices, to a connected graph with a crossing-free drawing while retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ Q.Connected ∧
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel Q.Adj := dQ
         G.edgeFinset ⊆ Q.edgeFinset) := by sorry
