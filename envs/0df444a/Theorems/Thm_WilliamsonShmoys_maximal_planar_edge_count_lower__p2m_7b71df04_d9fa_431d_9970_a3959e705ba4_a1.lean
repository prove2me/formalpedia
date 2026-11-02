-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:59:51.195072+00:00
-- url     : https://prove2.me/theorems/9f0d58b7-b6f9-47f0-b3be-8c258362d568
-- title:
--   Maximal planar edge-count lower bound
-- statement:
--   A graph with at least three vertices that is maximal among supergraphs drawable on the same vertex type has at least `3 |V| - 6` edges. The proof route is to establish connectedness and triangulation of the complementary faces: any face with more than three boundary edges would permit adding a missing diagonal while preserving the drawing, contradicting maximality. This child does not assume the target equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
