-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_edge_bound__p2m_06807de4_e70a_4ffd_9441_1bb5fb02d634_a1
-- name    : WilliamsonShmoys.planar_extension_edge_bound__p2m_06807de4_e70a_4ffd_9441_1bb5fb02d634_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:53.077791+00:00
-- url     : https://prove2.me/theorems/4144dd03-670b-4445-9630-6cae19c82121
-- title:
--   Planar edge-bound extension
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a drawable supergraph on the same vertices with at least $3|V|-6$ edges. The lemma supplies the extension used by maximality in the parent theorem. Its proof requires converting the continuous-arc drawing to a planar embedding and augmenting it while preserving the drawing predicate, including in disconnected cases; Euler’s formula then supplies the numerical bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_edge_bound__p2m_06807de4_e70a_4ffd_9441_1bb5fb02d634_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
