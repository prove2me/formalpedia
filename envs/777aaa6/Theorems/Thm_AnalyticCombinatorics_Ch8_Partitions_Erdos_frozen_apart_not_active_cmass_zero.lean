-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_frozen_apart_not_active_cmass_zero
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.frozen_apart_not_active_cmass_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:50:17.478295+00:00
-- url     : https://prove2.me/theorems/ba58cf7d-b979-4482-9dce-5c16cb6e27ed
-- title:
--   Frozen-apart rows have zero coalescence mass
-- statement:
--   Defines active high-rank versus frozen below-cutoff pairs and proves zero coalescence mass for frozen-apart rows. This obstructs applying an all-start drop premise to the killed kernel; it is not a convergence producer.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma frozen_apart_not_active_cmass_zero
--       (hfrozen : PointFrozenBelow P rnk J)
--       {x y : α} (hx : rnk x < J) (hy : rnk y < J) (hxy : x ≠ y) :
--       ¬ Active rnk J (x, y) ∧ cmass P rnk W x y = 0
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ActiveDomain.lean#L75. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ActiveDomain
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Active / frozen split for the killed pair coupling (TASK #9 layer A)

The all-start FK drop hypothesis is false for the killed partition chain because *frozen-apart*
below-cutoff pairs `(x,y)` with `x ≠ y` are absorbed point masses with zero common mass: the free
residual walk stays put, `cmass = 0`, and no drop set is ever hit.  This file isolates exactly those
rows.

We work with a finite state type `α`, a rank `rnk`, a window `W`, and a kernel `P` that is
*point-frozen below the cutoff* `J`: rows `x` with `rnk x < J` are the absorbing point mass at `x`
(`P x z = if z = x then 1 else 0`).  This is precisely the structure of `killedKer` on the finite
segment.  We define

  `Active J xy := J ≤ rnk xy.1 ∧ J ≤ rnk xy.2`

and prove that a frozen-apart counter-row (`rnk x < J`, `rnk y < J`, `x ≠ y`) is `¬ Active` and has
`cmass P rnk W x y = 0`.  Opus-authored.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W J : ℕ)

variable {P rnk W J}

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.frozen_apart_not_active_cmass_zero
    (hfrozen : PointFrozenBelow P rnk J)
    {x y : α} (hx : rnk x < J) (hy : rnk y < J) (hxy : x ≠ y) :
    ¬ Active rnk J (x, y) ∧ cmass P rnk W x y = 0 := by sorry
