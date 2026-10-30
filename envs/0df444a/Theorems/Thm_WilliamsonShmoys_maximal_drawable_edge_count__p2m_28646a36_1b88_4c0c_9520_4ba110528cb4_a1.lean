-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:13.584595+00:00
-- url     : https://prove2.me/theorems/9c5c2913-8662-47f3-b676-c48b7de0b279
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
