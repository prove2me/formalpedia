-- Prove2me | Theorems.Thm_mme_finite_indexed_exists_many_compatible_outer_division_free
-- name    : mme_finite_indexed_exists_many_compatible_outer_division_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T14:25:41.176336+00:00
-- url     : https://prove2.me/theorems/5ed4afbc-71c4-4d23-be57-350d95eb7243
-- title:
--   Division-free indexed averaging to distinct compatible outer objects
-- statement:
--   Let `Outer` be a finite family of outer objects and `Typical` a finite,
--   nonempty family of typical words.  For each outer object `I`, let
--   `Assignment(I)` be a finite set of exactly `N` assignments, and suppose that
--   assembling an outer object and one of its assignments produces a typical word.
--   Assume that, after fixing `I`, two assignments producing the same typical
--   word must be equal.
--
--   Then some typical word `small` is produced by sufficiently many distinct
--   outer objects that
--
--   ```text
--   |Outer| * N <= |Typical| *
--     |{I in Outer : some assignment of I assembles to small}|.
--   ```
--
--   This is the division-free maximum-at-least-average principle.  The
--   fixed-outer injectivity assumption is what makes the right side count distinct
--   outer objects rather than assignment incidences with multiplicity.
-- source:
--   Finite double-counting and maximum-fiber form of the averaging step in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Equation (22), printed p. 55.

import Mathlib

set_option autoImplicit false

theorem mme_finite_indexed_exists_many_compatible_outer_division_free
    {Outer Typical : Type*}
    [Finite Outer] [Finite Typical] [Nonempty Typical]
    (Assignment : Outer → Type*) [∀ I, Finite (Assignment I)]
    (assemble : (Σ I : Outer, Assignment I) → Typical)
    (N : ℕ) (hN : ∀ I, Nat.card (Assignment I) = N)
    (hinj : ∀ I, Function.Injective (fun A => assemble ⟨I, A⟩)) :
    ∃ small : Typical,
      Nat.card Outer * N ≤
        Nat.card Typical *
          Nat.card {I : Outer // ∃ A : Assignment I,
            assemble ⟨I, A⟩ = small} := by sorry
