-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:50.023522+00:00
-- url     : https://prove2.me/theorems/8d6b5728-c6cc-4920-a7cd-a91520c68320
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   A drawable simple graph with at least three vertices that has no proper drawable extension on the same vertex set has exactly 3|V|−6 edges. The proof route is to show maximality forces a triangulation, apply Euler’s formula and 3F = 2E, and use the at-least-three-vertices hypothesis in the planar topology argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      N.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ N.edgeFinset) :
    N.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
