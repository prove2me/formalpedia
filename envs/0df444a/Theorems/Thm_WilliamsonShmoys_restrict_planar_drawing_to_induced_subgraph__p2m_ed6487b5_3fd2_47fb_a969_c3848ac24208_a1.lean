-- Prove2me | Theorems.Thm_WilliamsonShmoys_restrict_planar_drawing_to_induced_subgraph__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
-- name    : WilliamsonShmoys.restrict_planar_drawing_to_induced_subgraph__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:42.175892+00:00
-- url     : https://prove2.me/theorems/37480a94-911f-4e66-956c-f017651fbcdc
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   Restricting a crossing-free drawing to any finset of vertices gives a crossing-free drawing of the induced subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.restrict_planar_drawing_to_induced_subgraph__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (s : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce (s : Set V)) := by
  sorry
