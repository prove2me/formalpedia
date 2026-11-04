-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:16.612183+00:00
-- url     : https://prove2.me/theorems/30d6faec-b0bf-4bef-98dc-af9f33dfa7ee
-- title:
--   Planar drawing edge upper bound
-- statement:
--   For a finite simple graph on at least three vertices, any crossing-free drawing as defined by `HasPlanarDrawingOn` has at most `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
