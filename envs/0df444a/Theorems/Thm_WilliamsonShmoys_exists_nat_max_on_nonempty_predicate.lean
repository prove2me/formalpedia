-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_nat_max_on_nonempty_predicate
-- name    : WilliamsonShmoys.exists_nat_max_on_nonempty_predicate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:07:20.092178+00:00
-- url     : https://prove2.me/theorems/d7dba2de-f511-41ab-80ac-7cce3146f53b
-- title:
--   A natural-valued function attains a maximum on a nonempty predicate over a finite type
-- statement:
--   For a finite type, every natural-valued score has a maximum among the elements satisfying any nonempty predicate. This handles the choice of an admissible graph with maximum edge count. It follows by filtering `Finset.univ` by the predicate and selecting a maximum of the score; the nonemptiness hypothesis ensures the filtered set is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_nat_max_on_nonempty_predicate
    {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by sorry
