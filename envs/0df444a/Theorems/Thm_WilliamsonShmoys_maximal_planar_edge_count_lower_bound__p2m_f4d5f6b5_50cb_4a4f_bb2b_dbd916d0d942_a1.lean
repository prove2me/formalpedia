-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:21.72858+00:00
-- url     : https://prove2.me/theorems/58b7864f-b594-4fea-9b4c-5ab78bff59aa
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   A drawable graph on at least three vertices that has no drawable edge extension on the same vertex set has at least 3|V|−6 edges. This supplies the lower-bound half missing from the planar upper bound. A proof route is to show maximality forces connectedness, complete the drawing to a triangulation, and use maximality to identify the completion with the original graph; Euler’s formula and triangular-face incidence then give the count. The connectedness, completion, and face-counting arguments for the given arc definition remain the substantial proof work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      M.edgeFinset ⊆ N.edgeFinset -> N.edgeFinset ⊆ M.edgeFinset)
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= M.edgeFinset.card := by sorry
