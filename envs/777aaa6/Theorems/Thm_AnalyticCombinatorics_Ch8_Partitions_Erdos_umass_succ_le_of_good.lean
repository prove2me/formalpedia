-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_umass_succ_le_of_good
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_succ_le_of_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:49:39.808401+00:00
-- url     : https://prove2.me/theorems/639746ee-d942-4ce9-bd2c-81bdbcdcfd37
-- title:
--   A conditional unmatched-mass recursion on good pairs
-- statement:
--   Per-step unmatched-mass recursion conditional on minorization on a Good predicate; it is not global coalescence.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem umass_succ_le_of_good (Good : α → α → Prop) [DecidableRel Good] (δ : ℝ) (hδ0 : 0 ≤ δ)
--       (hminor_good : ∀ x y, Good x y → δ ≤ cmass P rnk W x y) (t : ℕ) :
--       umass P rnk W i j (t + 1)
--         ≤ umass P rnk W i j t
--           - δ * ∑ x, ∑ y, (if Good x y then Umat P rnk W i j t x y else 0)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/GoodHiRecursion.lean#L30. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: minorization on a sub-predicate ⟹ umass recursion

For the KILLED chain, the Doeblin minorization `δ ≤ cmass` holds only on the *active high-rank* window
`GoodHi` (where `Pker_window_minor`/brick 79 applies), NOT on absorbed/low-rank pairs.  This brick
generalizes the per-step contraction to any sub-predicate `Good` on which the minorization holds:

  `umass (t+1) ≤ umass t − δ · (Good-window mass of Umat t)`.

It follows from `umass_succ_eq` (`umass(t+1) = umass(t) − ∑ Umat·cmass`) since the coalescence mass
`∑ Umat·cmass ≥ δ · ∑_{Good} Umat`.  Then the (banked) CoalesceBridge consumes this with `g = ĝ` the
conditioned `Good`-fraction.  Deterministic finite-sum.  Opus-authored.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)
include hPnn hPmass

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_succ_le_of_good (Good : α → α → Prop) [DecidableRel Good] (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor_good : ∀ x y, Good x y → δ ≤ cmass P rnk W x y) (t : ℕ) :
    umass P rnk W i j (t + 1)
      ≤ umass P rnk W i j t
        - δ * ∑ x, ∑ y, (if Good x y then Umat P rnk W i j t x y else 0) := by sorry
