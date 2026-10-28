-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_predicate_extension
-- name    : WilliamsonShmoys.finite_maximal_predicate_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:24:14.683099+00:00
-- url     : https://prove2.me/theorems/c6d59c96-4851-4ae5-8739-692c4b448117
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any predicate on simple graphs over a finite vertex type, if a graph H satisfies the predicate, there is a predicate-satisfying supergraph K of H that has no strictly larger predicate-satisfying supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_predicate_extension
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H) :
    ∃ K : SimpleGraph V, P K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, P L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        ∀ u v, L.Adj u v → K.Adj u v) := by sorry
