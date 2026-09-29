-- Prove2me | solution 1 for RLHF.objective_eq_sub_kl_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:41:22.680683+00:00
-- url     : https://prove2.me/submissions/058d3756-c19b-4c4b-b741-7731eab982e0

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
theorem solution{β : ℝ} {r p q : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hq : IsDist q) :
    objective β r p q = β * Real.log (partition β r p) - β * klDiv q (gibbsPolicy β r p) := by
  have hZ := partition_pos (β := β) (r := r) hp
  have hterm : ∀ y, q y * Real.log (q y / gibbsPolicy β r p y)
      = q y * Real.log (q y / p y) - q y * (r y / β) + q y * Real.log (partition β r p) := by
    intro y
    rcases eq_or_lt_of_le (hq.1 y) with hq0 | hqpos
    · rw [← hq0]; ring
    · have hpy := hp.1 y
      have hpi : gibbsPolicy β r p y = p y * Real.exp (r y / β) / partition β r p := rfl
      have hpipos : 0 < gibbsPolicy β r p y := gibbsPolicy_pos hp y
      rw [Real.log_div (ne_of_gt hqpos) (ne_of_gt hpipos),
        Real.log_div (ne_of_gt hqpos) (ne_of_gt hpy), hpi,
        Real.log_div (by positivity) (ne_of_gt hZ), Real.log_mul (ne_of_gt hpy) (by positivity),
        Real.log_exp]
      ring
  have hsum : klDiv q (gibbsPolicy β r p)
      = klDiv q p - (∑ y, q y * r y) / β + Real.log (partition β r p) := by
    unfold klDiv
    rw [Finset.sum_congr rfl (fun y _ => hterm y)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]
    congr 1
    congr 1
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [hsum, objective]
  field_simp
  ring
