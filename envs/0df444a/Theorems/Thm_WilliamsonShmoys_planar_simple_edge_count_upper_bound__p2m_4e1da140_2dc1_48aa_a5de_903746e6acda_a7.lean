-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_count_upper_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
-- name    : WilliamsonShmoys.planar_simple_edge_count_upper_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T04:02:54.156052+00:00
-- url     : https://prove2.me/theorems/0e207e25-7f30-47af-be70-fcc8041d5eb3
-- title:
--   Simple planar graph edge-count upper bound
-- statement:
--   A finite simple graph with the supplied planar drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_count_upper_bound__p2m_4e1da140_2dc1_48aa_a5de_903746e6acda_a7
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
