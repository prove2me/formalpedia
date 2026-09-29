-- Prove2me | Theorems.Thm_mme_finset_prescribed_fiber_function_card
-- name    : mme_finset_prescribed_fiber_function_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:28:18.784274+00:00
-- url     : https://prove2.me/theorems/ee80b9dd-02dc-4eac-93df-1c780edd241c
-- title:
--   Functions with prescribed finite fibers form a multinomial-sized finset
-- statement:
--   Let α and ι be finite sets, and prescribe a nonnegative fiber size k(i) for each i in ι, with total equal to |α|. The number of functions g:α→ι whose fiber over every i has size k(i) is the multinomial coefficient indexed by k.
-- source:
--   Standard multinomial enumeration of functions with prescribed fibers; finset interface for the exact Table-2 profile count.

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Set.Card

open scoped BigOperators

set_option autoImplicit false

theorem mme_finset_prescribed_fiber_function_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (k : ι → ℕ) (hsum : ∑ i, k i = Fintype.card α) :
    (Finset.univ.filter fun g : α → ι ↦
      ∀ i, Fintype.card {a // g a = i} = k i).card =
      Nat.multinomial Finset.univ k := by
  sorry
