-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:44.424176+00:00
-- url     : https://prove2.me/theorems/23ef3f28-c786-4f0c-b412-311d85f11230
-- title:
--   Euler upper bound for a finite planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates the Euler-counting upper bound used by the parent; the hypothesis is retained so the bound has the correct small-order boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
