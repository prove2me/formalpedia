-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion__p2m_715939c0_b6e9_4c03_a6f3_4355f1ffabc5_a1
-- name    : WilliamsonShmoys.maximal_planar_completion__p2m_715939c0_b6e9_4c03_a6f3_4355f1ffabc5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T18:50:03.096328+00:00
-- url     : https://prove2.me/theorems/0fdafab4-3fd6-4759-8b58-e983a7df1ef3
-- title:
--   Planar drawing extends to the planar edge lower bound
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is at least 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion__p2m_715939c0_b6e9_4c03_a6f3_4355f1ffabc5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
