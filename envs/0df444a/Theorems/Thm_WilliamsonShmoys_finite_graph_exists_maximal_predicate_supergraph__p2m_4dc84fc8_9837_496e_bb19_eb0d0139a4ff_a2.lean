-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_exists_maximal_predicate_supergraph__p2m_4dc84fc8_9837_496e_bb19_eb0d0139a4ff_a2
-- name    : WilliamsonShmoys.finite_graph_exists_maximal_predicate_supergraph__p2m_4dc84fc8_9837_496e_bb19_eb0d0139a4ff_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:21:16.571597+00:00
-- url     : https://prove2.me/theorems/89fd35df-cd6b-4294-8c96-ab91a44a302d
-- title:
--   Finite maximal supergraph for a predicate
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, if it holds of L, there is a predicate-satisfying supergraph of L with no proper predicate-satisfying edge extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_exists_maximal_predicate_supergraph__p2m_4dc84fc8_9837_496e_bb19_eb0d0139a4ff_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P L) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    exists M : SimpleGraph V,
      L.edgeFinset ⊆ M.edgeFinset /\
      P M /\
      forall N : SimpleGraph V,
        (forall u v, M.Adj u v -> N.Adj u v) ->
        P N ->
        forall u v, N.Adj u v -> M.Adj u v := by
  sorry
