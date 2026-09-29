-- Prove2me | Theorems.Thm_mme_fintype_fixed_fiber_function_card
-- name    : mme_fintype_fixed_fiber_function_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:47:53.566035+00:00
-- url     : https://prove2.me/theorems/76f874c3-6bb7-40f0-af07-031b1e6f2fa0
-- title:
--   Functions with prescribed finite fibers are counted by a multinomial coefficient
-- statement:
--   Let $f:\alpha\to\iota$ be a function between finite sets. The number of functions $g:\alpha\to\iota$ having exactly the same fiber cardinalities as $f$ is
--
--   $$
--   \frac{|\alpha|!}{\prod_{i\in\iota}|f^{-1}(i)|!}.
--   $$
--
--   Equivalently, a realizable prescribed histogram on a finite alphabet is counted by its multinomial coefficient. This form is useful for exact type-class counts in tensor-power and laser-method arguments.
-- source:
--   Finite orbit--stabilizer applied to the natural symmetric-group action on words with a fixed content vector.

import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient

open Equiv MulAction

theorem mme_fintype_fixed_fiber_function_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (f : α → ι) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} =
            Fintype.card {a // f a = i}} =
      (Fintype.card α).factorial /
        ∏ i, (Fintype.card {a // f a = i}).factorial := by
  sorry
