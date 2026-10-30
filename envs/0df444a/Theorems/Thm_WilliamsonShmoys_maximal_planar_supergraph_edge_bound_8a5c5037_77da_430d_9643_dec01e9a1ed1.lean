-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_bound_8a5c5037_77da_430d_9643_dec01e9a1ed1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_bound_8a5c5037_77da_430d_9643_dec01e9a1ed1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:11:03.18235+00:00
-- url     : https://prove2.me/theorems/9b959836-a5ce-4be0-befe-a14662618d09
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on those vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_bound_8a5c5037_77da_430d_9643_dec01e9a1ed1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
