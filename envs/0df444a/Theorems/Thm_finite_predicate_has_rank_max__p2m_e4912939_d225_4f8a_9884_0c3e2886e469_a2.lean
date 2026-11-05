-- Prove2me | Theorems.Thm_finite_predicate_has_rank_max__p2m_e4912939_d225_4f8a_9884_0c3e2886e469_a2
-- name    : finite_predicate_has_rank_max__p2m_e4912939_d225_4f8a_9884_0c3e2886e469_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:54:16.331549+00:00
-- url     : https://prove2.me/theorems/3229f54f-3843-49cd-8ec4-9f9ee48ad656
-- title:
--   A finite predicate admits a rank maximizer
-- statement:
--   On a finite type, if a predicate has at least one witness, then some witness maximizes any natural-valued rank. This supplies the selection step for a planar supergraph with the greatest number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_predicate_has_rank_max__p2m_e4912939_d225_4f8a_9884_0c3e2886e469_a2
    {α : Type} [Fintype α] (P : α → Prop) (rank : α → Nat)
    (a : α) (ha : P a) :
    ∃ b, P b ∧ ∀ c, P c → rank c ≤ rank b := by sorry
