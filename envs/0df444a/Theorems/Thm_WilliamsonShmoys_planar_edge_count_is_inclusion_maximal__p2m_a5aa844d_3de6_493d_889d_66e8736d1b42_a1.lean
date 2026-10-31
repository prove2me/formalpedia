-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_is_inclusion_maximal__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
-- name    : WilliamsonShmoys.planar_edge_count_is_inclusion_maximal__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T11:22:24.821749+00:00
-- url     : https://prove2.me/theorems/7f8156d0-59cd-483d-b914-1d18d842c166
-- title:
--   The extremal planar edge count forces inclusion maximality
-- statement:
--   If a drawable finite simple graph on at least three vertices has exactly the planar extremal number of edges, then every drawable graph on the same vertices containing its edges has the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_is_inclusion_maximal__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (hsub : H.edgeSet ⊆ K.edgeSet) :
    K.edgeSet = H.edgeSet := by sorry
