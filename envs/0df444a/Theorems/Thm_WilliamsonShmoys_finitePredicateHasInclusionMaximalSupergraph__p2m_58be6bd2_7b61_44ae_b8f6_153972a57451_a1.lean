-- Prove2me | Theorems.Thm_WilliamsonShmoys_finitePredicateHasInclusionMaximalSupergraph__p2m_58be6bd2_7b61_44ae_b8f6_153972a57451_a1
-- name    : WilliamsonShmoys.finitePredicateHasInclusionMaximalSupergraph__p2m_58be6bd2_7b61_44ae_b8f6_153972a57451_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:17:07.425057+00:00
-- url     : https://prove2.me/theorems/da045366-6f1b-41a4-a133-bb1cf88eaf46
-- title:
--   Finite predicate has an inclusion-maximal supergraph
-- statement:
--   For any predicate on graphs over a finite ordered vertex type, if the predicate holds for K, then K has a supergraph satisfying the predicate that is maximal under edge inclusion among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finitePredicateHasInclusionMaximalSupergraph__p2m_58be6bd2_7b61_44ae_b8f6_153972a57451_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : SimpleGraph V → Prop) (hP : P K) :
    ∃ (H : SimpleGraph V), K ≤ H ∧ P H ∧
      ∀ (J : SimpleGraph V), H ≤ J → P J → J ≤ H := by sorry
