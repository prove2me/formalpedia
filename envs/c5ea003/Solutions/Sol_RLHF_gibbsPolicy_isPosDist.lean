-- Prove2me | solution 1 for RLHF.gibbsPolicy_isPosDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:50.924879+00:00
-- url     : https://prove2.me/submissions/7f999dd1-f68a-4a44-8823-6685cf68379e

-- Sol generated from NumberTheory/RLHFGibbsVariational.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Theorems.Thm_RLHF_partition_pos

/-!
# The Gibbs variational principle for KL-regularized RLHF

This module is the root of the RLHF thread of the catalog.  It sets up the finite
KL-regularized alignment problem and proves the Gibbs variational principle that all the
downstream files use.

For a finite response space `Ω`, a reward model `r : Ω → ℝ`, a strictly positive reference
(SFT) policy `p : Ω → ℝ` and a KL coefficient `β > 0`, the RLHF objective at a policy `q` is

```
objective β r p q = 𝔼_q[r] − β · KL(q ‖ p).
```

Main results.

* `RLHF.kl_nonneg` — Gibbs' inequality: `KL(q ‖ p) ≥ 0` for a distribution `q` and a
  positive distribution `p`.
* `RLHF.kl_eq_zero_iff` — the equality case: `KL(q ‖ p) = 0 ↔ q = p`.
* `RLHF.objective_eq_sub_kl_gibbs` — the *pivot identity*
  `objective β r p q = β log Z(β) − β · KL(q ‖ π_β)`, where `π_β` is the Gibbs (tilted)
  policy and `Z(β) = ∑_y p y · exp(r y / β)` the partition function.
* `RLHF.variational_principle` and `RLHF.variational_strict` — consequently `β log Z` is the
  optimal value of the RLHF objective, attained *only* at the Gibbs policy
  (`RLHF.objective_gibbs`).
* `RLHF.reference_le_free_energy` — RLHF never hurts: the optimal value dominates the value
  of the reference policy.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. Policies -/




/-! ## 2. Kullback–Leibler divergence -/





/-! ## 3. Partition function, Gibbs policy and the RLHF objective -/




variable [Nonempty Ω]


theorem gibbsPolicy_pos {β : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p) (y : Ω) :
    0 < gibbsPolicy β r p y := by
  have hZ := partition_pos (β := β) (r := r) hp
  have := hp.1 y
  unfold gibbsPolicy
  positivity








open RLHF in
theorem solution{β : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p) :
    IsPosDist (gibbsPolicy β r p) := by
  refine ⟨gibbsPolicy_pos hp, ?_⟩
  have hZ := partition_pos (β := β) (r := r) hp
  unfold gibbsPolicy
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hZ)
