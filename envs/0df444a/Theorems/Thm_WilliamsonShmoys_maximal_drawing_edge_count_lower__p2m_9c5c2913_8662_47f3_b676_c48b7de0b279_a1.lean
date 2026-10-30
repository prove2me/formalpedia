-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
-- name    : WilliamsonShmoys.maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:30.2598+00:00
-- url     : https://prove2.me/theorems/ce0752f6-2cc0-436b-9908-f6f14786777a
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   An inclusion-maximal graph with a planar drawing on at least three vertices has at least 3|V|−6 edges. The lower-bound direction is the maximality/triangulation step: planar augmentation on the same vertex set would contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
