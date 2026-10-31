-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:57.010861+00:00
-- url     : https://prove2.me/theorems/1d331833-450a-47b6-a107-4143d686327f
-- title:
--   Maximal drawable graphs have at least the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable edge additions has at least 3|V|−6 edges. Triangulating its faces yields the bound; when there are exactly three vertices, maximality forces all three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
