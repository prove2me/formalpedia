-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T11:58:36.610946+00:00
-- url     : https://prove2.me/theorems/f02ef8ad-5db5-4334-91a0-6b5d944fa80f
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal planar graph on at least three vertices has exactly $3|V|-6$ edges. This supplies the edge-count conclusion for the maximal supergraph in the parent. A proof route is to show maximality forces a connected plane embedding with every face triangular, then apply Euler’s formula and count each edge twice among face boundaries. The substantive remaining work is to formalize those topological facts for the supplied continuous-arc definition of HasPlanarDrawingOn; the at-least-three hypothesis is retained for the standard triangulation count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
