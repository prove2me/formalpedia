-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_e4fb4528_3000_447a_a91c_bbceedbe6374_a1
-- name    : WilliamsonShmoys_planar_drawing_edge_bound__p2m_e4fb4528_3000_447a_a91c_bbceedbe6374_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:08:45.994653+00:00
-- url     : https://prove2.me/theorems/55c0bceb-ffb6-44c6-a362-90e494710496
-- title:
--   Euler edge bound for a finite graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices that admits the specified crossing-free drawing has at most three times its number of vertices minus six edges. Maximality is not required; the child isolates the general planar edge bound from the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_planar_drawing_edge_bound__p2m_e4fb4528_3000_447a_a91c_bbceedbe6374_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
