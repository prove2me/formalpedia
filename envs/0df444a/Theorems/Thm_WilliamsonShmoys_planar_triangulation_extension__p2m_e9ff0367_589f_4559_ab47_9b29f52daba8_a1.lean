-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_e9ff0367_589f_4559_ab47_9b29f52daba8_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_e9ff0367_589f_4559_ab47_9b29f52daba8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:21.208488+00:00
-- url     : https://prove2.me/theorems/ebf573df-7a41-4cc7-8e00-a5df5b7401f0
-- title:
--   Triangulated extension of a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. This also covers disconnected input graphs; the vertex-count hypothesis excludes the small cases where the maximal planar edge formula does not apply. A proof route is to add drawable edges until the graph is maximal, establish that the resulting graph is connected with triangular faces, and derive the edge count from Euler’s formula. The remaining core work is formalizing this planar augmentation and face-count argument from the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_e9ff0367_589f_4559_ab47_9b29f52daba8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeFinset ⊆ M.edgeFinset ∧
      M.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
