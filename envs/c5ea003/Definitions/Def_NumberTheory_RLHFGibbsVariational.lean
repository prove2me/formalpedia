-- Prove2me | Definitions.Def_NumberTheory_RLHFGibbsVariational
-- name    : NumberTheory_RLHFGibbsVariational
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:16.292004+00:00
-- url     : https://prove2.me/theorems/612954a1-113d-4e07-8b77-f5b2a6216bf8
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFGibbsVariational
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFGibbsVariational`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFGibbsVariational.lean by skeleton subtraction
import Mathlib

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

namespace RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. Policies -/

/-- A probability distribution on the finite response space. -/
def IsDist (q : Ω → ℝ) : Prop := (∀ y, 0 ≤ q y) ∧ ∑ y, q y = 1

/-- A strictly positive probability distribution (an admissible SFT reference policy). -/
def IsPosDist (p : Ω → ℝ) : Prop := (∀ y, 0 < p y) ∧ ∑ y, p y = 1


/-! ## 2. Kullback–Leibler divergence -/

/-- The Kullback–Leibler divergence of `q` from `p`. -/
noncomputable def klDiv (q p : Ω → ℝ) : ℝ := ∑ y, q y * Real.log (q y / p y)




/-! ## 3. Partition function, Gibbs policy and the RLHF objective -/

/-- The partition function `Z(β) = ∑_y p y · exp (r y / β)`. -/
noncomputable def partition (β : ℝ) (r p : Ω → ℝ) : ℝ := ∑ y, p y * Real.exp (r y / β)

/-- The tilted (Gibbs) policy `π_β(y) ∝ p y · exp (r y / β)`. -/
noncomputable def gibbsPolicy (β : ℝ) (r p : Ω → ℝ) : Ω → ℝ :=
  fun y => p y * Real.exp (r y / β) / partition β r p

/-- The KL-regularized RLHF objective. -/
noncomputable def objective (β : ℝ) (r p q : Ω → ℝ) : ℝ :=
  (∑ y, q y * r y) - β * klDiv q p

variable [Nonempty Ω]









end RLHF


