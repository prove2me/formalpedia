-- Prove2me | Theorems.Thm_UniversalRedundancy_tvDist_powLaw_le_one_sub_pow
-- name    : UniversalRedundancy.tvDist_powLaw_le_one_sub_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:02:10.521311+00:00
-- url     : https://prove2.me/theorems/b0108a66-abff-461a-a3c2-ed79597e662e
-- title:
--   Sharp `n`-sample bound.
-- statement:
--   **Sharp `n`-sample bound.**  Total variation amplifies geometrically, not
--   linearly: `d_TV(p^{⊗n}, q^{⊗n}) ≤ 1 − (1 − d_TV(p, q))^n`.  The witness is the
--   `n`-fold independent product of the maximal coupling.
--
--   ```lean
--   theorem UniversalRedundancy.tvDist_powLaw_le_one_sub_pow{p q : X → ℝ} (hp : ∑ x, p x = 1)
--       (hq : ∑ x, q x = 1) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (n : ℕ) :
--       tvDist (powLaw p n) (powLaw q n) ≤ 1 - (1 - tvDist p q) ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/Tensorization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/Tensorization.lean#L83

-- Thm stub generated from MachineLearning/TotalVariation/Tensorization.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_Tensorization
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
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

theorem UniversalRedundancy.tvDist_powLaw_le_one_sub_pow{p q : X → ℝ} (hp : ∑ x, p x = 1)
    (hq : ∑ x, q x = 1) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (n : ℕ) :
    tvDist (powLaw p n) (powLaw q n) ≤ 1 - (1 - tvDist p q) ^ n := by sorry
