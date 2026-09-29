-- Prove2me | solution 1 for RLHF.gibbs_eq_iff_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:08:39.807089+00:00
-- url     : https://prove2.me/submissions/67dc73a3-3637-4bb4-aa89-80db3dd3a860

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

omit [Nonempty Ω] in
theorem partition_shift {β c : ℝ} {r p : Ω → ℝ} :
    partition β (fun y => r y + c) p = Real.exp (c / β) * partition β r p := by
  unfold partition
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [show (r y + c) / β = r y / β + c / β by ring, Real.exp_add]
  ring

/-- Adding a constant to the reward model does not change the aligned policy. -/
theorem gibbsPolicy_shift {β c : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p) :
    gibbsPolicy β (fun y => r y + c) p = gibbsPolicy β r p := by
  have hZ := partition_pos (β := β) (r := r) hp
  funext y
  unfold gibbsPolicy
  rw [partition_shift (r := r) (c := c),
    show (r y + c) / β = r y / β + c / β by ring, Real.exp_add]
  have hc : Real.exp (c / β) ≠ 0 := Real.exp_ne_zero _
  field_simp


/-! ## 2. The DPO reparametrization -/



/-! ## 3. Composition of RLHF steps -/


/-! ## 4. Arithmetic corollary: Dirichlet exponents add -/

variable {A B : ℕ}




open RLHF in
theorem solution{β : ℝ} {r₁ r₂ p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p) :
    gibbsPolicy β r₁ p = gibbsPolicy β r₂ p ↔ ∃ c : ℝ, ∀ y, r₁ y = r₂ y + c := by
  constructor
  · intro hEq
    have hZ₁ := partition_pos (β := β) (r := r₁) hp
    have hZ₂ := partition_pos (β := β) (r := r₂) hp
    refine ⟨β * Real.log (partition β r₁ p / partition β r₂ p), fun y => ?_⟩
    have hy : p y * Real.exp (r₁ y / β) / partition β r₁ p
        = p y * Real.exp (r₂ y / β) / partition β r₂ p := congrFun hEq y
    have hpy := hp.1 y
    rw [div_eq_div_iff (ne_of_gt hZ₁) (ne_of_gt hZ₂)] at hy
    have key : p y * (Real.exp (r₁ y / β) * partition β r₂ p)
        = p y * (Real.exp (r₂ y / β) * partition β r₁ p) := by
      rw [← mul_assoc, ← mul_assoc]; exact hy
    have hexp : Real.exp (r₁ y / β) * partition β r₂ p
        = Real.exp (r₂ y / β) * partition β r₁ p := mul_left_cancel₀ (ne_of_gt hpy) key
    have hratio : Real.exp (r₁ y / β - r₂ y / β) = partition β r₁ p / partition β r₂ p := by
      rw [Real.exp_sub, div_eq_div_iff (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ₂)]
      linarith [hexp]
    have hlog : r₁ y / β - r₂ y / β = Real.log (partition β r₁ p / partition β r₂ p) := by
      rw [← hratio, Real.log_exp]
    field_simp at hlog ⊢
    linarith [hlog]
  · rintro ⟨c, hc⟩
    have : r₁ = fun y => r₂ y + c := funext hc
    rw [this]
    exact gibbsPolicy_shift hp
