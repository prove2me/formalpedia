-- Prove2me | solution 1 for cantor_from_lawvere
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:42:21.550591+00:00
-- url     : https://prove2.me/submissions/5f90b15a-8c53-4f75-bf32-2572584b54f2

import Mathlib.Logic.Function.Basic

open Function

theorem solution (A : Type*) :
    ¬ ∃ f : A → (A → Prop), Surjective f := by
  rintro ⟨f, hf⟩
  -- `Set A` is defeq to `A → Prop`, so this is Cantor's theorem.
  exact cantor_surjective (f : A → Set A) hf
