-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:14.016109+00:00
-- url     : https://prove2.me/theorems/e3717bab-3827-442d-b57a-788e3af1d41c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges, expressed without subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
