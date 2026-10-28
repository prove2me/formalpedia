-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_nat_score_maximum
-- name    : WilliamsonShmoys.finite_nat_score_maximum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:53:49.579135+00:00
-- url     : https://prove2.me/theorems/a0494058-0408-4d80-a33a-492426d2b33f
-- title:
--   Maximum of a natural-valued score on a nonempty finite feasible family
-- statement:
--   For a finite type, every nonempty feasible family has an element maximizing any natural-valued score, with the chosen feasible element scoring at least as high as the supplied feasible witness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_nat_score_maximum
    {α : Type} [Fintype α]
    (P : α → Prop) (score : α → Nat) (x : α) (hx : P x) :
    ∃ y : α, P y ∧ score x ≤ score y ∧ ∀ z : α, P z → score z ≤ score y := by sorry
