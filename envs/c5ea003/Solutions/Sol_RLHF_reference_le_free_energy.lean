-- Prove2me | solution 1 for RLHF.reference_le_free_energy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:55:29.279003+00:00
-- url     : https://prove2.me/submissions/4d8382b4-0681-4f6c-839f-147156143898

-- Sol generated from NumberTheory/RLHFGibbsVariational.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Theorems.Thm_RLHF_IsPosDist_isDist
import Theorems.Thm_RLHF_kl_eq_zero_iff
import Theorems.Thm_RLHF_variational_principle

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










open RLHF in
theorem solution{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p) :
    ∑ y, p y * r y ≤ β * Real.log (partition β r p) := by
  have h := variational_principle (β := β) (r := r) hβ hp hp.isDist
  rw [objective, (kl_eq_zero_iff hp.isDist hp).2 rfl] at h
  simpa using h
