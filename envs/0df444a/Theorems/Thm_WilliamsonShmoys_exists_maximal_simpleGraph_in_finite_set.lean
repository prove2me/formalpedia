-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_in_finite_set
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_in_finite_set
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:19:15.974749+00:00
-- url     : https://prove2.me/theorems/db41d2a7-4962-4f11-9274-281d211f81cb
-- title:
--   A finite nonempty family of simple graphs has an inclusion-maximal member
-- statement:
--   Every nonempty finite family of simple graphs on a finite vertex type contains a member maximal under edge inclusion. It removes the finite maximization step from the target. An independent proof route selects a graph with maximum finite edge-set cardinality and shows that a proper edge extension would have strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_simpleGraph_in_finite_set
    {V : Type} [Fintype V] [Fintype (SimpleGraph V)]
    (S : Set (SimpleGraph V)) (hSfin : S.Finite) (hSne : S.Nonempty) :
    ∃ W, W ∈ S ∧
      ∀ X, X ∈ S →
        (∀ u v, W.Adj u v → X.Adj u v) →
        ∀ u v, X.Adj u v → W.Adj u v := by
  sorry
