-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximum_of_bounded_nat_predicate__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
-- name    : WilliamsonShmoys.exists_maximum_of_bounded_nat_predicate__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:30.928374+00:00
-- url     : https://prove2.me/theorems/df3c96ec-64b2-497c-b281-8363d999a677
-- title:
--   Maximum of a bounded nonempty set of natural numbers
-- statement:
--   Every nonempty predicate on natural numbers whose values are bounded above by B has a greatest satisfying value.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximum_of_bounded_nat_predicate__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1 (P : Nat → Prop) (B : Nat) (hbounded : ∀ n, P n → n ≤ B) (hnonempty : ∃ n, P n) : ∃ n, P n ∧ ∀ m, P m → m ≤ n := by sorry
