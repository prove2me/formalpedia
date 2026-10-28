-- Prove2me | Theorems.Thm_finite_simpleGraph_supergraph_maximal
-- name    : finite_simpleGraph_supergraph_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:57:36.836315+00:00
-- url     : https://prove2.me/theorems/b691b33b-b080-4b05-8f86-a682f163cd3e
-- title:
--   Finite maximality among graph supergraphs
-- statement:
--   For any property P of graphs on a finite linearly ordered vertex type, every graph satisfying P has a P supergraph that is maximal among P supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_supergraph_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
        (∀ K : SimpleGraph V, P K → H ≤ K → K = H) := by
  sorry
