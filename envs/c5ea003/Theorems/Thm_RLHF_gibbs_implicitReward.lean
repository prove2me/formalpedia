-- Prove2me | Theorems.Thm_RLHF_gibbs_implicitReward
-- name    : RLHF.gibbs_implicitReward
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:46:16.584548+00:00
-- url     : https://prove2.me/theorems/b386ebe0-3271-48ff-b27e-784b9fbe86ed
-- title:
--   DPO reparametrization.
-- statement:
--   **DPO reparametrization.**  Every strictly positive policy is the exact RLHF optimum
--   for its own implicit reward.
--
--   ```lean
--   theorem RLHF.gibbs_implicitReward{β : ℝ} {p q : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
--       (hq : IsPosDist q) : gibbsPolicy β (implicitReward β p q) p = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFRewardIdentifiability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFRewardIdentifiability.lean#L88

-- Thm stub generated from NumberTheory/RLHFRewardIdentifiability.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFRewardIdentifiability
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy

/-!
# Reward identifiability, DPO reparametrization, and the semigroup of RLHF steps

Three structural theorems about the KL-regularized RLHF map `r ↦ π_β = gibbsPolicy β r p`:

* `RLHF.gibbsPolicy_shift` / `RLHF.gibbs_eq_iff_shift` — the aligned policy determines the
  reward model **exactly up to an additive constant**: reward models are identifiable only
  modulo `ℝ`.
* `RLHF.gibbs_implicitReward` — every positive policy is the RLHF optimum of the *implicit*
  reward `β log (q/p)` (the DPO reparametrization); combined with the previous item this
  makes `r ↦ π_β` a bijection between rewards-modulo-constants and positive policies.
* `RLHF.gibbs_compose` — iterating RLHF adds rewards:
  `gibbsPolicy β r₂ (gibbsPolicy β r₁ p) = gibbsPolicy β (r₁ + r₂) p`.
  Thus RLHF steps carry an action of the additive group of reward models.

Arithmetic payoff (`RLHF.zeta_policy_compose`): for Dirichlet rewards on a smooth-number
response space, composing two RLHF steps at sharpness `s₁` and `s₂` produces exactly the
zeta policy at sharpness `s₁ + s₂`.  The alignment semigroup acts on Dirichlet exponents by
addition, i.e. by multiplication of the corresponding Dirichlet series weights.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Shift invariance and identifiability -/




/-! ## 2. The DPO reparametrization -/


omit [Nonempty Ω] in

theorem RLHF.gibbs_implicitReward{β : ℝ} {p q : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hq : IsPosDist q) : gibbsPolicy β (implicitReward β p q) p = q := by sorry
