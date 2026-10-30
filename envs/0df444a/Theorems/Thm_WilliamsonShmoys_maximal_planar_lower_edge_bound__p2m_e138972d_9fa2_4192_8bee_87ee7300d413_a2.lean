-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
-- name    : WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:40:54.436826+00:00
-- url     : https://prove2.me/theorems/3e25b6a0-4b21-4d35-9051-eedb215386d1
-- title:
--   Maximal drawable graphs have at least 3n − 6 edges
-- statement:
--   A drawable graph maximal under edge addition on the same vertex set, with at least three vertices, has at least 3n − 6 edges. The proof route is to use maximality to force a triangulated plane embedding and then apply Euler’s formula and face-edge incidence counting. The n ≥ 3 hypothesis is essential to the stated natural-number subtraction bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by sorry
