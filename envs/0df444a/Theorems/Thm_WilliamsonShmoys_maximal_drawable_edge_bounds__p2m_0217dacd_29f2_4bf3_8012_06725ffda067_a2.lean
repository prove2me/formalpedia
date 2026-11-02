-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
-- name    : WilliamsonShmoys.maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:37:23.357668+00:00
-- url     : https://prove2.me/theorems/eb33baa9-c4b4-4164-a447-f726a2fe0cc5
-- title:
--   Edge bounds for a maximal drawable graph
-- statement:
--   For a maximal drawable supergraph K on at least three vertices, the original graph H has no more edges than K, and K has between |V|−2 and 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     letI : DecidableRel K.Adj := Classical.decRel K.Adj
     letI : Fintype H.edgeSet := Fintype.ofFinite H.edgeSet
     letI : Fintype K.edgeSet := Fintype.ofFinite K.edgeSet
     H.edgeFinset.card ≤ K.edgeFinset.card ∧
     Fintype.card V ≤ K.edgeFinset.card + 2 ∧
     K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
