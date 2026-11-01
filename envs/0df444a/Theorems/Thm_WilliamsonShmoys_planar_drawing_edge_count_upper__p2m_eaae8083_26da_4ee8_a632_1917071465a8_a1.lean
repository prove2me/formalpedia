-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:17.447167+00:00
-- url     : https://prove2.me/theorems/d2c50861-0fd8-4da0-94ee-613d34c69ea2
-- title:
--   Upper edge count for a planar drawing
-- statement:
--   Every finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler and face-counting bound; the lower bound on the number of vertices excludes the small cases where the formula needs separate treatment.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
