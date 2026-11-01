-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:22.52571+00:00
-- url     : https://prove2.me/theorems/62c40d5f-afd7-4bfc-ad24-9691a3287af2
-- title:
--   Planar upper bound for maximal graph edge count
-- statement:
--   A finite simple planar graph on at least three vertices has at most 3n−6 edges; maximality is retained in the hypotheses to match the parent interface, though the bound itself does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
