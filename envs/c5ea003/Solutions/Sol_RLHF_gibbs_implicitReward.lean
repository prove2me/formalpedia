-- Prove2me | solution 1 for RLHF.gibbs_implicitReward
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:13:30.444069+00:00
-- url     : https://prove2.me/submissions/520af95d-69ca-4fc9-b61f-23ab00a2910d

-- Sol generated from NumberTheory/RLHFRewardIdentifiability.lean
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



/-! ## 3. Composition of RLHF steps -/


/-! ## 4. Arithmetic corollary: Dirichlet exponents add -/

variable {A B : ℕ}




open RLHF in
omit [Nonempty Ω] in
theorem solution{β : ℝ} {p q : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hq : IsPosDist q) : gibbsPolicy β (implicitReward β p q) p = q := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hexp : ∀ y, p y * Real.exp (implicitReward β p q y / β) = q y := by
    intro y
    have hpy := hp.1 y
    have hqy := hq.1 y
    unfold implicitReward
    rw [show β * Real.log (q y / p y) / β = Real.log (q y / p y) by field_simp [hβ0],
      Real.exp_log (by positivity)]
    field_simp
  have hZ : partition β (implicitReward β p q) p = 1 := by
    unfold partition
    rw [Finset.sum_congr rfl (fun y _ => hexp y), hq.2]
  funext y
  unfold gibbsPolicy
  rw [hZ, div_one, hexp y]
