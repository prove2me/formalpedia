-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ActiveDomain
-- name    : AnalyticCombinatorics_Ch8_Partitions_ActiveDomain
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:44:56.642546+00:00
-- url     : https://prove2.me/theorems/3b41b834-ff69-4ffd-b823-5e437af52396
-- title:
--   Active Domain
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ActiveDomain.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W J : ℕ)

/-- The active domain for the killed coupling at cutoff `J`: both ranks are at the cutoff or above. -/
def Active (xy : α × α) : Prop := J ≤ rnk xy.1 ∧ J ≤ rnk xy.2

/-- A kernel is *point-frozen below `J`*: each below-cutoff row is the absorbing point mass. -/
def PointFrozenBelow : Prop :=
  ∀ x z, rnk x < J → P x z = (if z = x then 1 else 0)

variable {P rnk W J}


end AnalyticCombinatorics.Ch8.Partitions.Erdos


