-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a5
-- name    : WilliamsonShmoys.maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:27:07.802014+00:00
-- url     : https://prove2.me/theorems/078d72d1-c4b8-4d42-8ead-9d2688891836
-- title:
--   Edge bounds for a maximal drawable graph
-- statement:
--   If K is drawable and maximal among drawable supergraphs of H on at least three finite ordered vertices, then H has no more edges than K, and K has between |V|−2 and 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H <= K)
    (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    H.edgeFinset.card <= K.edgeFinset.card ∧
      Fintype.card V <= K.edgeFinset.card + 2 ∧
      K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
