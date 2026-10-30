-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
-- name    : WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:04.599637+00:00
-- url     : https://prove2.me/theorems/943b5aff-fabf-479f-acf2-f330b4b95e8b
-- title:
--   A predicate on a finite partial order has a maximal member
-- statement:
--   In a finite partial order, every nonempty predicate-defined subset contains an element with no distinct larger member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2 {alpha : Type} [PartialOrder alpha] [Finite alpha] (P : alpha -> Prop) (hP : Exists fun x => P x) : Exists fun x => P x /\ forall y, P y -> LE.le x y -> y = x := by sorry
