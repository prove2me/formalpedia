-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:42.983105+00:00
-- url     : https://prove2.me/theorems/13012d9d-6550-4fe7-b932-cfc62eea8364
-- title:
--   Edge upper bound for a finite simple planar graph
-- statement:
--   Every finite simple graph on at least three vertices with a drawing as defined has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
