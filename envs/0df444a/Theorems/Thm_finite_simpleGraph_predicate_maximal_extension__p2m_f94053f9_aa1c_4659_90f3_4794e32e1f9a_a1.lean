-- Prove2me | Theorems.Thm_finite_simpleGraph_predicate_maximal_extension__p2m_f94053f9_aa1c_4659_90f3_4794e32e1f9a_a1
-- name    : finite_simpleGraph_predicate_maximal_extension__p2m_f94053f9_aa1c_4659_90f3_4794e32e1f9a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:38.656295+00:00
-- url     : https://prove2.me/theorems/0e19d874-7057-4601-b85f-ef819fc05a61
-- title:
--   Finite simple graphs have maximal predicate extensions
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_predicate_maximal_extension__p2m_f94053f9_aa1c_4659_90f3_4794e32e1f9a_a1
    {U : Type} [Fintype U]
    (H : SimpleGraph U) (P : SimpleGraph U → Prop) (hP : P H) :
    ∃ K : SimpleGraph U, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph U, K ≤ L → P L → K = L := by sorry
