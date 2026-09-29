-- Prove2me | Theorems.Thm_UniversalRedundancy_one_sub_pow_le_nsmul
-- name    : UniversalRedundancy.one_sub_pow_le_nsmul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:00:12.726571+00:00
-- url     : https://prove2.me/theorems/e0e29ccb-591c-4a96-a66d-5d9d9acf0554
-- title:
--   Bernoulli's inequality in the form we need: the geometric amplification law
-- statement:
--   Bernoulli's inequality in the form we need: the geometric amplification law
--   is never worse than the hybrid bound.
--
--   ```lean
--   theorem UniversalRedundancy.one_sub_pow_le_nsmul{t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
--       ∀ n : ℕ, 1 - (1 - t) ^ n ≤ n * t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/Tensorization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/Tensorization.lean#L116

-- Thm stub generated from MachineLearning/TotalVariation/Tensorization.lean
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

theorem UniversalRedundancy.one_sub_pow_le_nsmul{t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ n : ℕ, 1 - (1 - t) ^ n ≤ n * t := by sorry
