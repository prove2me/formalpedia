-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_property__p2m_d861cb11_4d1d_4208_9ad9_8ec6eefefc53_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_finite_property__p2m_d861cb11_4d1d_4208_9ad9_8ec6eefefc53_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:23.606385+00:00
-- url     : https://prove2.me/theorems/d088ed5a-b36e-43ae-b237-b97f1c99884a
-- title:
--   Finite graphs admit maximal predicate-preserving supergraphs
-- statement:
--   For any predicate on simple graphs over a finite ordered vertex type, if G satisfies the predicate, there is a predicate-satisfying supergraph H with a decidable adjacency relation that is maximal among predicate-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_supergraph_for_finite_property__p2m_d861cb11_4d1d_4208_9ad9_8ec6eefefc53_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : SimpleGraph V → Prop)
    (hG : P G) :
    ∃ H : SimpleGraph V, ∃ (_ : DecidableRel H.Adj),
      G.edgeFinset ⊆ H.edgeFinset ∧
      P H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        P K → K = H := by
  sorry
