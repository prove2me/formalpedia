-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:35:16.1644+00:00
-- url     : https://prove2.me/theorems/e11a3f5a-70fe-4c53-9ca5-c876b8f1fe13
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that is maximal among drawable supergraphs on the same vertices has at least 3|V|−6 edges. This removes the maximality half of the target. A proof route is to show that maximality forces every face of a planar embedding to be triangular—otherwise a missing chord can be added inside that face—then apply Euler counting. The |V|≥3 hypothesis and the full supergraph maximality condition are preserved; without the former, the stated edge formula need not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * (Fintype.card V : Int) - 6 ≤ (K.edgeSet.ncard : Int) := by sorry
