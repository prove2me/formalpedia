-- Prove2me | Theorems.Thm_RLHF_variational_strict
-- name    : RLHF.variational_strict
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:49:48.013774+00:00
-- url     : https://prove2.me/theorems/3efc5c16-3337-480e-acec-dbf6cef5b0f3
-- title:
--   Uniqueness of the optimum.
-- statement:
--   **Uniqueness of the optimum.**  Every policy other than the Gibbs policy is strictly
--   suboptimal.
--
--   ```lean
--   theorem RLHF.variational_strict{β : ℝ} {r p q : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
--       (hq : IsDist q) (hne : q ≠ gibbsPolicy β r p) :
--       objective β r p q < β * Real.log (partition β r p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFGibbsVariational.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFGibbsVariational.lean#L199

-- Thm stub generated from NumberTheory/RLHFGibbsVariational.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational

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

theorem RLHF.variational_strict{β : ℝ} {r p q : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hq : IsDist q) (hne : q ≠ gibbsPolicy β r p) :
    objective β r p q < β * Real.log (partition β r p) := by sorry
