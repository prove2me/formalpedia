-- Prove2me | Theorems.Thm_aharoni_korman_false
-- name    : aharoni_korman_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:19:26.945009+00:00
-- url     : https://prove2.me/theorems/94904be3-7f40-4a99-8cf7-bcef2c46be0e
-- title:
--   aharoni korman false: aharoni korman false
-- statement:
--   The Aharoni–Korman conjecture (sometimes called the fishbone conjecture) says that every partial
--   order satisfies one of the following:
--   - It contains an infinite antichain
--   - It contains a chain C, and has a partition into antichains such that every part meets C.
--
--   In November 2024, Hollom disproved this conjecture.
--
--   This statement says that it is not the case that every partially ordered set satisfies one of the
--   above conditions.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1269-L1282
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1269-L1282

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff

theorem aharoni_korman_false :
    ¬ ∀ (α : Type) (_ : PartialOrder α),
        (∃ A : Set α, IsAntichain (· ≤ ·) A ∧ A.Infinite) ∨
        (∃ C : Set α, IsChain (· ≤ ·) C ∧
         ∃ S : Set (Set α), Setoid.IsPartition S ∧
          ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) := by sorry
