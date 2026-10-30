-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_has_triangulation_edge_count__p2m_80d3c120_40ab_4263_83fa_69737aacfbab_a1
-- name    : WilliamsonShmoys.planar_extension_has_triangulation_edge_count__p2m_80d3c120_40ab_4263_83fa_69737aacfbab_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:10.888014+00:00
-- url     : https://prove2.me/theorems/57f967cc-933c-4757-9db5-f93a97c57bfc
-- title:
--   Planar extension with triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set whose number of edges is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_extension_has_triangulation_edge_count__p2m_80d3c120_40ab_4263_83fa_69737aacfbab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
