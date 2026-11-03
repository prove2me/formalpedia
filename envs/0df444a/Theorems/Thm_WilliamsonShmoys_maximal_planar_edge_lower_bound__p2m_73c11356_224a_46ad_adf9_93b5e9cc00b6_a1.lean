-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:32:59.703212+00:00
-- url     : https://prove2.me/theorems/f2e67bcd-d844-4f8f-86df-68d56c93483a
-- title:
--   Edge-maximal planar graphs satisfy the Euler edge lower bound
-- statement:
--   An edge-maximal simple planar graph on a finite linearly ordered vertex type with at least three vertices has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_73c11356_224a_46ad_adf9_93b5e9cc00b6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
