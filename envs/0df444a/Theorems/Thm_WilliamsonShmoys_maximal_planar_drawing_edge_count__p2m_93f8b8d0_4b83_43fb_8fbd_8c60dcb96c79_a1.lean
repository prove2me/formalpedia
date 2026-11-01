-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_93f8b8d0_4b83_43fb_8fbd_8c60dcb96c79_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_93f8b8d0_4b83_43fb_8fbd_8c60dcb96c79_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:43.698867+00:00
-- url     : https://prove2.me/theorems/eaae8083-26da-4ee8-a632-1917071465a8
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A finite simple graph on at least three vertices that is maximal among graphs admitting a crossing-free drawing on the same ordered vertex type has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_93f8b8d0_4b83_43fb_8fbd_8c60dcb96c79_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
