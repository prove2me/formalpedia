-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_has_maximal_edge_count_f3b6ee58
-- name    : WilliamsonShmoys.inclusion_maximal_planar_has_maximal_edge_count_f3b6ee58
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:41:16.379089+00:00
-- url     : https://prove2.me/theorems/dc092f72-7ddd-408d-8976-f47c28b5eb72
-- title:
--   An inclusion-maximal planar graph has the triangulated edge count
-- statement:
--   A simple planar graph on at least three vertices that has no strict planar supergraph on the same vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.inclusion_maximal_planar_has_maximal_edge_count_f3b6ee58
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ K' : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K' →
      K.edgeSet ⊆ K'.edgeSet →
      K'.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
