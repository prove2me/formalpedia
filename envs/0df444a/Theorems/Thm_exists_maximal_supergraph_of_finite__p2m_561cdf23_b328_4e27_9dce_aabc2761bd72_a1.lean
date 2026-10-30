-- Prove2me | Theorems.Thm_exists_maximal_supergraph_of_finite__p2m_561cdf23_b328_4e27_9dce_aabc2761bd72_a1
-- name    : exists_maximal_supergraph_of_finite__p2m_561cdf23_b328_4e27_9dce_aabc2761bd72_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:42.779991+00:00
-- url     : https://prove2.me/theorems/22578bdf-83eb-4b2f-94e2-098c8b1dd64b
-- title:
--   Finite maximality for graph predicates
-- statement:
--   For a graph on a finite vertex type, any graph predicate satisfied by G has a supergraph H satisfying the predicate that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_supergraph_of_finite__p2m_561cdf23_b328_4e27_9dce_aabc2761bd72_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H) := by sorry
