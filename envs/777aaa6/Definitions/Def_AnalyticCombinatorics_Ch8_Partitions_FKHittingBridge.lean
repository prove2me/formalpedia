-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_FKHittingBridge
-- name    : AnalyticCombinatorics_Ch8_Partitions_FKHittingBridge
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:46:02.457547+00:00
-- url     : https://prove2.me/theorems/3f351658-f6d0-47af-851e-504972630a23
-- title:
--   F K Hitting Bridge
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/FKHittingBridge.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Hitting-to-FK block drop

This file contains the finite-state algebraic corollary used by the concrete
block-drop task: if the free walk hits a drop set with uniformly positive
probability during a block, then the Feynman--Kac block weight has a uniform
drop.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {S : Type*} [Fintype S]

/-- Free-walk probability to hit `A` during one of the first `M` departure states. -/
def hitProb (Q : S → S → ℝ) (A : S → Prop) [DecidablePred A] : ℕ → S → ℝ
  | 0 => fun _ => 0
  | M + 1 => fun s => if A s then 1 else ∑ z, Q s z * hitProb Q A M z


end AnalyticCombinatorics.Ch8.Partitions.Erdos


