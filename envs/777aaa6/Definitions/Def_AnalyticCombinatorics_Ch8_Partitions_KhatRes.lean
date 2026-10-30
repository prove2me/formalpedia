-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KhatRes
-- name    : AnalyticCombinatorics_Ch8_Partitions_KhatRes
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:48:37.831597+00:00
-- url     : https://prove2.me/theorems/03a75c88-4c73-4067-9de9-524cf9234e77
-- title:
--   Khat Res
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/KhatRes.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Conditioned residual kernel

`Kres` is the substochastic residual product kernel whose row mass is `1 - cmass`.
This file normalizes it to a stochastic conditioned-residual kernel.  Rows with
`cmass = 1` are parked at the current pair; the analytic application only uses
the `cmass < 1` rows, but the parked rows make the pair kernel stochastic
globally.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- The conditioned residual kernel, in four-coordinate form. -/
def KhatRes (x y a b : α) : ℝ :=
  if cmass P rnk W x y < 1 then
    Kres P rnk W x y a b / (1 - cmass P rnk W x y)
  else if a = x ∧ b = y then 1 else 0

/-- The conditioned residual kernel as a kernel on pair states. -/
def KhatResPair (xy zw : α × α) : ℝ :=
  KhatRes P rnk W xy.1 xy.2 zw.1 zw.2

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)


end AnalyticCombinatorics.Ch8.Partitions.Erdos


