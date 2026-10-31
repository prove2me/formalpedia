-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:37.622654+00:00
-- url     : https://prove2.me/theorems/fed4729c-77e3-4492-a45e-1ab93cbddb9e
-- title:
--   Edge bound for a maximal planar graph
-- statement:
--   A finite simple graph with at least three vertices that is maximal among graphs admitting the supplied crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
