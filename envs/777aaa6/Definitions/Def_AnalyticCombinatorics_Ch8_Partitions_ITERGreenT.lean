-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERGreenT
-- name    : AnalyticCombinatorics_Ch8_Partitions_ITERGreenT
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:05:35.769092+00:00
-- url     : https://prove2.me/theorems/d00df0da-309f-421f-9c73-47fe38f8e176
-- title:
--   I T E R Green T
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ITERGreenT.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin: the finite-horizon Green potential is a subsolution for free

ChatGPT R7's key observation: the finite-`T` truncated Green potential

  `greenT T (x,y) = ∑_{t<T} (KresAct^[t] goodIndic) (x,y)`

(expected window occupation over `T` residual steps) is a Poisson **subsolution** of the residual
kernel `Kres` *automatically* — no recurrence needed.  The geometric/Poisson identity

  `KresAct (greenT T) = greenT T − goodIndic + KresAct^[T] goodIndic`

has a nonnegative tail, so `KresAct (greenT T) ≥ greenT T − goodIndic`, i.e. exactly the hypothesis the
banked `occupation_ge_green_tight` consumes.  This file banks that structural fact (pure finite-sum
algebra).  The entire remaining wall then collapses to the single expected-local-time lower bound
`greenT T (i,j) ≥ (1−ε)/δ` for high-rank comparable starts (the recurrence content), plus the ITER
instantiation to the killed Erdős kernel.  Opus-authored (vehicle ChatGPT R7).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

/-- Window indicator on pairs. -/
def goodIndic : α → α → ℝ := fun x y => if GoodW rnk W x y then (1 : ℝ) else 0

/-- One application of the residual kernel as an operator on pair-functions. -/
def KresAct (f : α → α → ℝ) : α → α → ℝ :=
  fun x y => ∑ a, ∑ b, Kres P rnk W x y a b * f a b

/-- Finite-horizon Green potential: expected window occupation over `T` residual steps. -/
def greenT (T : ℕ) : α → α → ℝ :=
  fun x y => ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t] (goodIndic rnk W) x y

end AnalyticCombinatorics.Ch8.Partitions.Erdos


