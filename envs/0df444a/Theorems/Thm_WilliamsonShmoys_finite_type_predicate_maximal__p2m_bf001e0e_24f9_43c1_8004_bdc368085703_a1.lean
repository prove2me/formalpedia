-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1
-- name    : WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:53.464068+00:00
-- url     : https://prove2.me/theorems/ba9d7771-f9d6-416b-bf3a-b00f1c408698
-- title:
--   A predicate on a finite partial order has a maximal member
-- statement:
--   Every nonempty predicate-defined subset of a finite partial order contains a member with no strictly larger member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1 {alpha : Type} [PartialOrder alpha] [Finite alpha] (P : alpha -> Prop) (hP : Exists fun x => P x) : Exists fun x => P x /\ forall y, P y -> LE.le x y -> y = x := by sorry
