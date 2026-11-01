-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:33:46.796213+00:00
-- url     : https://prove2.me/theorems/26140903-fcb8-4c7c-a0cc-72edca446c76
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that is maximal among planar supergraphs has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
