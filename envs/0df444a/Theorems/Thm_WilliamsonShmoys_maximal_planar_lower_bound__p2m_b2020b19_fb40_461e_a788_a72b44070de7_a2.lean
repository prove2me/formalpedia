-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
-- name    : WilliamsonShmoys.maximal_planar_lower_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:30:00.609728+00:00
-- url     : https://prove2.me/theorems/715939c0-b6e9-4c03-a6f3-4355f1ffabc5
-- title:
--   Maximality forces the planar lower bound
-- statement:
--   A drawable graph with at least three vertices that has no drawable strict supergraph on the same vertex type has at least three times its number of vertices minus six edges. The intended proof shows maximality forces connectedness and triangular faces, then uses Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_lower_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
