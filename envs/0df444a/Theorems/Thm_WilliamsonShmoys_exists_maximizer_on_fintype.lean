-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximizer_on_fintype
-- name    : WilliamsonShmoys.exists_maximizer_on_fintype
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:25:09.831528+00:00
-- url     : https://prove2.me/theorems/4572127c-d5be-4d73-adf1-b8d3508817c3
-- title:
--   A predicate on a finite type has a score maximizer
-- statement:
--   If a predicate holds for at least one element of a finite type, then its satisfying elements contain one maximizing any linearly ordered score.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximizer_on_fintype
    {α β : Type} [Fintype α] [DecidableEq α] [LinearOrder β]
    (P : α → Prop) (score : α → β) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → score b ≤ score a := by sorry
