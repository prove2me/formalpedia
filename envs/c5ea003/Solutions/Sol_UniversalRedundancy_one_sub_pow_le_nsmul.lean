-- Prove2me | solution 1 for UniversalRedundancy.one_sub_pow_le_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:28:00.37162+00:00
-- url     : https://prove2.me/submissions/5aa77930-b769-4e11-91b7-2d44c6ddee25

-- Sol generated from MachineLearning/TotalVariation/Tensorization.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_Tensorization
import Definitions.Def_MachineLearning_TotalVariation_Testing
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharp `n`-sample amplification: `d_TV(p^{⊗n}, q^{⊗n}) ≤ 1 − (1 − d_TV)^n`

`Testing` derived the textbook hybrid bound `d_TV(p^{⊗n}, q^{⊗n}) ≤ n·d_TV(p, q)`.
That bound is *vacuous* as soon as `n ≥ 1/d_TV`: it exceeds `1`, while total
variation never does.  This file replaces it by the sharp geometric law

`d_TV(p^{⊗n}, q^{⊗n}) ≤ 1 − (1 − d_TV(p, q))^n`,

which stays inside `[0, 1]` for every `n`, is strictly stronger than the linear
bound for all `n ≥ 2` (`one_sub_pow_lt_nsmul`), and has the right asymptotics:
`n` samples buy an advantage `1 − e^{−n d_TV}`, not `n d_TV`.

The proof is a genuine *transport* argument and is only available because
`Coupling` supplied the maximal coupling: couple each of the `n` coordinates
maximally and independently.  The resulting product coupling agrees in every
coordinate with probability exactly `(1 − d_TV)^n`, and `tvDist_le_disagreeProb`
converts that into the bound.  Neither the `ℓ¹` estimate nor the event
supremum alone can see this.

## Main results

* `powCoupling`, `isCoupling_powCoupling` — independent product of couplings;
* `sum_diag_powCoupling` — its agreement probability is the `n`-th power;
* `tvDist_powLaw_le_one_sub_pow` — the sharp amplification law;
* `tvDist_powLaw_le_one` — `n` samples never distinguish perfectly unless one
  sample already does;
* `one_sub_pow_le_nsmul`, `one_sub_pow_lt_nsmul` — the new bound dominates the
  hybrid bound, strictly for `n ≥ 2`.

## Application keywords

tensorization, hybrid argument, maximal coupling, sample complexity,
amplification, indistinguishability
-/


open Finset

open UniversalRedundancy

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Independent products of couplings -/




/-! ## The sharp amplification law -/



/-! ## The geometric bound dominates the linear one -/






open UniversalRedundancy in
theorem solution{t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ n : ℕ, 1 - (1 - t) ^ n ≤ n * t := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hb0 : (0:ℝ) ≤ 1 - t := by linarith
      have hb1 : (1 - t) ^ n ≤ 1 := pow_le_one₀ hb0 (by linarith)
      have hb0n : (0:ℝ) ≤ (1 - t) ^ n := pow_nonneg hb0 n
      have hstep : (1 - t) ^ (n + 1) = (1 - t) ^ n - t * (1 - t) ^ n := by
        rw [pow_succ]; ring
      rw [hstep]
      push_cast
      nlinarith [ih, hb1, hb0n]
