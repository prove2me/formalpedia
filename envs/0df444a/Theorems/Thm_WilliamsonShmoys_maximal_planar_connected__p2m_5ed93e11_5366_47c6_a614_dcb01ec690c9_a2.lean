-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_connected__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
-- name    : WilliamsonShmoys.maximal_planar_connected__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:57.333358+00:00
-- url     : https://prove2.me/theorems/d040595c-f679-4c6d-8e62-deaf65883107
-- title:
--   A maximal drawable graph is connected
-- statement:
--   A finite graph with a crossing-free drawing that is maximal among drawable supergraphs on the same vertex set is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_connected__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    M.Connected := by sorry
