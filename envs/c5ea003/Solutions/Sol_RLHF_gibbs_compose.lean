-- Prove2me | solution 1 for RLHF.gibbs_compose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:08:39.28447+00:00
-- url     : https://prove2.me/submissions/a2834b55-1506-4c83-8151-b702d3955aca

-- Sol generated from NumberTheory/RLHFRewardIdentifiability.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFRewardIdentifiability
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_partition_pos

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



/-! ## 3. Composition of RLHF steps -/


/-! ## 4. Arithmetic corollary: Dirichlet exponents add -/

variable {A B : ℕ}




open RLHF in
theorem solution{β : ℝ} {r₁ r₂ p : Ω → ℝ} (hp : IsPosDist p) :
    gibbsPolicy β r₂ (gibbsPolicy β r₁ p) = gibbsPolicy β (fun y => r₁ y + r₂ y) p := by
  have hZ₁ := partition_pos (β := β) (r := r₁) hp
  have hZ₁₂ := partition_pos (β := β) (r := fun y => r₁ y + r₂ y) hp
  set Z₁ := partition β r₁ p with hZ₁def
  set Z₁₂ := partition β (fun y => r₁ y + r₂ y) p with hZ₁₂def
  have hnum : ∀ y, gibbsPolicy β r₁ p y * Real.exp (r₂ y / β)
      = (p y * Real.exp ((r₁ y + r₂ y) / β)) / Z₁ := by
    intro y
    unfold gibbsPolicy
    rw [show (r₁ y + r₂ y) / β = r₁ y / β + r₂ y / β by ring, Real.exp_add]
    rw [← hZ₁def]
    field_simp
  have hstep : partition β r₂ (gibbsPolicy β r₁ p) = Z₁₂ / Z₁ := by
    unfold partition
    rw [Finset.sum_congr rfl (fun y _ => hnum y), ← Finset.sum_div]
    rfl
  funext y
  show gibbsPolicy β r₁ p y * Real.exp (r₂ y / β) / partition β r₂ (gibbsPolicy β r₁ p)
      = p y * Real.exp ((r₁ y + r₂ y) / β) / Z₁₂
  rw [hnum y, hstep]
  field_simp
