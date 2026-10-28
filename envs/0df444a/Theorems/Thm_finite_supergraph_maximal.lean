-- Prove2me | Theorems.Thm_finite_supergraph_maximal
-- name    : finite_supergraph_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:43:39.001696+00:00
-- url     : https://prove2.me/theorems/29dd9734-65e1-4acb-a092-8c76851cdfae
-- title:
--   Maximal predicate-preserving supergraph on a finite vertex type
-- statement:
--   For a finite vertex type, any graph satisfying a predicate has a supergraph satisfying the same predicate that is maximal among predicate-satisfying supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_supergraph_maximal
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P K) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧ P K' ∧
        ∀ L : SimpleGraph V, K' ≤ L → P L → L ≤ K' := by sorry
