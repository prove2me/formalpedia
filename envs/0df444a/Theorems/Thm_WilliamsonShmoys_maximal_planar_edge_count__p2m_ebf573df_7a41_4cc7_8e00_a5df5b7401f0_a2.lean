-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:01.095577+00:00
-- url     : https://prove2.me/theorems/f4d5f6b5-50cb-4a4f-bb2b-dbd916d0d942
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict edge extension has exactly $3|V|-6$ edges. This isolates the embedding and Euler-count argument from choosing a maximal extension. A proof route is to use maximality to establish connectedness and triangular faces in a planar embedding, then count vertices, edges, and faces with Euler's formula. That topology argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N →
      M.edgeFinset ⊆ N.edgeFinset → N.edgeFinset ⊆ M.edgeFinset)
    (hcard : 3 <= Fintype.card V) :
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
