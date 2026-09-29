-- Prove2me | solution 1 for UniversalRedundancy.tvDist_powLaw_le_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:50:34.132231+00:00
-- url     : https://prove2.me/submissions/d29d126b-62c7-4a00-8078-88afb1a9ec2d

-- Sol generated from MachineLearning/TotalVariation/Tensorization.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_Tensorization
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_disagreeProb_eq_one_sub_diag
import Theorems.Thm_UniversalRedundancy_disagreeProb_maxCoupling
import Theorems.Thm_UniversalRedundancy_isCoupling_maxCoupling
import Theorems.Thm_UniversalRedundancy_isCoupling_powCoupling
import Theorems.Thm_UniversalRedundancy_sum_powLaw
import Theorems.Thm_UniversalRedundancy_tvDist_le_disagreeProb
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



omit [DecidableEq X] in
/-- The `n` coordinates agree simultaneously with probability `(∑ₓ c x x)^n`. -/
theorem sum_diag_powCoupling (c : X → X → ℝ) (n : ℕ) :
    ∑ v, powCoupling c n v v = (∑ x, c x x) ^ n := by
  have h := Fintype.prod_sum (fun (_ : Fin n) (x : X) => c x x)
  simp only [powCoupling]
  rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The sharp amplification law -/



/-! ## The geometric bound dominates the linear one -/






open UniversalRedundancy in
theorem solution{p q : X → ℝ} (hp : ∑ x, p x = 1)
    (hq : ∑ x, q x = 1) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (n : ℕ) :
    tvDist (powLaw p n) (powLaw q n) ≤ 1 - (1 - tvDist p q) ^ n := by
  have hcoup : IsCoupling p q (maxCoupling p q) :=
    isCoupling_maxCoupling hp hq hp0 hq0
  have hdiag : ∑ x, maxCoupling p q x x = 1 - tvDist p q := by
    have h1 := disagreeProb_eq_one_sub_diag hcoup hp
    have h2 := disagreeProb_maxCoupling hp hq hp0 hq0
    linarith [h1, h2]
  have hn := isCoupling_powCoupling hcoup n
  have hle := tvDist_le_disagreeProb (sum_powLaw hp n) (sum_powLaw hq n) hn
  have hdis : disagreeProb (powCoupling (maxCoupling p q) n)
      = 1 - (1 - tvDist p q) ^ n := by
    rw [disagreeProb_eq_one_sub_diag hn (sum_powLaw hp n),
      sum_diag_powCoupling, hdiag]
  linarith [hle, hdis.le, hdis.ge]
