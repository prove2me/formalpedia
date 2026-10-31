-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:36.711918+00:00
-- url     : https://prove2.me/theorems/46fe5fa5-fbe5-4667-8617-73807c0b1344
-- title:
--   Edge upper bound for a finite simple planar graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. This is the Euler-formula upper bound and is reusable independently of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
