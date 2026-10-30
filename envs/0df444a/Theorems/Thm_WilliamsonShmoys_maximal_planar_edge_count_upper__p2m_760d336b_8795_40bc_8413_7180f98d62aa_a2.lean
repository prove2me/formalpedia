-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:21.972971+00:00
-- url     : https://prove2.me/theorems/ddd64127-46c6-4ff5-ad6f-47496ad35234
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    H.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
