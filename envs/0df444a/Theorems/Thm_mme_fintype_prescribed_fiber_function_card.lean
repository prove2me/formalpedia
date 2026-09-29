-- Prove2me | Theorems.Thm_mme_fintype_prescribed_fiber_function_card
-- name    : mme_fintype_prescribed_fiber_function_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:03:31.335804+00:00
-- url     : https://prove2.me/theorems/3d1dbb77-fa28-4035-8dcc-5f1bc2a77e4e
-- title:
--   Finite functions with a prescribed histogram are counted by a multinomial coefficient
-- statement:
--   Let $k_i$ be nonnegative integers indexed by a finite alphabet $\iota$, with total $\sum_i k_i=|\alpha|$. The number of functions $g:\alpha\to\iota$ whose fiber above every $i$ has exactly $k_i$ elements is the multinomial coefficient
--
--   $$
--   \frac{|\alpha|!}{\prod_i k_i!}.
--   $$
--
--   The total-size hypothesis is used to construct a canonical word with this histogram; the result then follows from the fixed-fiber orbit--stabilizer count.
-- source:
--   Finite multinomial counting, reduced to orbit--stabilizer for the symmetric-group action on words with fixed content.

import Theorems.Thm_mme_fintype_fixed_fiber_function_card

open Equiv

theorem mme_fintype_prescribed_fiber_function_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (k : ι → ℕ) (hsum : ∑ i, k i = Fintype.card α) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} = k i} =
      (Fintype.card α).factorial / ∏ i, (k i).factorial := by
  sorry
