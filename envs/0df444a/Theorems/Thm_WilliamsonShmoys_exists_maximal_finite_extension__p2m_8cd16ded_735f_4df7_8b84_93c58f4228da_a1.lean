-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_finite_extension__p2m_8cd16ded_735f_4df7_8b84_93c58f4228da_a1
-- name    : WilliamsonShmoys.exists_maximal_finite_extension__p2m_8cd16ded_735f_4df7_8b84_93c58f4228da_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:53.458778+00:00
-- url     : https://prove2.me/theorems/5ce86dee-a51b-43d9-9c16-6a53f5f31031
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For a finite vertex type, every graph satisfying a property has a supergraph satisfying that property which is maximal under graph extension. There are finitely many simple graphs on the vertex type, so choose an eligible supergraph with the greatest number of edges. If an eligible graph extended it strictly, its edge count would be greater, a contradiction. This applies even when the property is not hereditary; the eligible family is nonempty because it contains `H`. The child removes the finite maximization argument from the parent, leaving only its direct instantiation with the planar-drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_finite_extension__p2m_8cd16ded_735f_4df7_8b84_93c58f4228da_a1
    {V : Type} [Fintype V] (H : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hH : P H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ P J ∧
      ∀ K : SimpleGraph V, J ≤ K → P K → K = J := by
  sorry
