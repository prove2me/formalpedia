-- Prove2me | solution 1 for HyperAwareness11D.card_activeRows_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:11:11.799193+00:00
-- url     : https://prove2.me/submissions/331d029c-0e39-485f-8496-03425a2f90b0

-- Sol generated from MachineLearning/HyperAwareness11D/Injectivity.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_exists_pos_scale
import Theorems.Thm_HyperAwareness11D_relu_of_nonpos

/-!
# Hyper-Awareness I: the exact width threshold for lossless 11-dimensional ReLU perception

This file answers, *exactly*, the central question of the research mission:

> How wide must a single ReLU layer be in order to process an 11-dimensional perception
> vector **without any dimensional reduction loss** (i.e. injectively)?

The answer proved here is **22 = 2 · 11**, and both directions are established:

* `HyperAwareness11D.two_mul_le_card_of_injective` — *lower bound.*  If a ReLU layer
  `x ↦ (relu (⟪wᵢ, x⟫ + bᵢ))ᵢ` on `ℝⁿ` is injective, then the number of output units is at
  least `2n`.  Specialised: an injective ReLU perception layer on `ℝ¹¹` needs `≥ 22` units.
* `HyperAwareness11D.doubleLayer_injective` — *upper bound.*  The "positive/negative split"
  layer `x ↦ (x⁺, x⁻)` with exactly `2n` units is injective, and is even *linearly*
  invertible (`HyperAwareness11D.doubleLayer_reconstruct`).
* `HyperAwareness11D.isLeast_width_11` — combining the two: `22` is the *least* width of an
  injective ReLU layer on 11-dimensional perception vectors.

## Structure of the lower bound proof

The argument is a hybrid of linear algebra, elementary real analysis and a finite
combinatorial duality step, and it avoids any measure theory:

1. `exists_generic_direction` (algebra: one-variable polynomials over an infinite field):
   there is a direction `u` with `⟪wᵢ, u⟫ ≠ 0` for every nonzero row `wᵢ`, obtained by
   evaluating the product of the row polynomials `∑ⱼ wᵢⱼ Xʲ` off its finite root set.
2. `card_activeRows_ge` (linear algebra + a perturbation argument): at any point `x` where
   no nonzero row is exactly at its kink, the *active* rows must have rank `n`; otherwise a
   kernel vector `v` of the active rows can be added to `x` (scaled small enough that the
   inactive rows stay inactive) without changing the output, contradicting injectivity.
   Rank `n` forces at least `n` active rows.
3. `two_mul_le_card_of_injective` (duality): far out along `±u` the active sets are exactly
   the rows with `⟪wᵢ, u⟫ > 0` resp. `< 0`; these two sets are **disjoint** and each has at
   least `n` elements, so the layer has at least `2n` units.

Step 3 is where the factor `2` — and hence the sharp constant `22` in dimension `11` — comes
from: a ReLU unit can only "see" one half-space, so a full 11-dimensional percept needs a
complete positive *and* a complete negative frame.
-/

open HyperAwareness11D

open Finset

noncomputable section

open scoped Classical

/-! ## Basic definitions -/





variable {ι ι' : Type*} {n : ℕ}




lemma preAct_add_smul (W : ι → Fin n → ℝ) (b : ι → ℝ) (x v : Fin n → ℝ) (t : ℝ) (i : ι) :
    preAct W b (x + t • v) i = preAct W b x i + t * ∑ j, W i j * v j := by
  simp only [preAct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hj : ∀ j, W i j * (x j + t * v j) = W i j * x j + t * (W i j * v j) := fun j => by ring
  simp only [hj, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring


/-! ## Two elementary scaling lemmas -/



/-! ## Genericity: a direction transverse to every nonzero row -/


/-! ## The local rank bound -/


/-! ## The sharp lower bound `width ≥ 2n` -/





/-! ## The matching construction: the positive/negative split layer -/










open HyperAwareness11D in
theorem solution[Fintype ι] (W : ι → Fin n → ℝ) (b : ι → ℝ)
    (hinj : Function.Injective (reluLayer W b)) (x : Fin n → ℝ)
    (hx : ∀ i, (∀ j, W i j = 0) ∨ preAct W b x i ≠ 0) :
    n ≤ (ActiveRows W b x).card := by
  classical
  set A := ActiveRows W b x with hA
  set L : (Fin n → ℝ) →ₗ[ℝ] ({i // i ∈ A} → ℝ) :=
    { toFun := fun v i => ∑ j, W i.1 j * v j
      map_add' := by
        intro v w; funext i
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c v; funext i
        simp [Finset.mul_sum, mul_left_comm] } with hL
  have hker : ∀ v : Fin n → ℝ, L v = 0 → v = 0 := by
    intro v hv
    have hvA : ∀ i ∈ A, (∑ j, W i j * v j) = 0 := by
      intro i hi
      have hcong := congrFun hv ⟨i, hi⟩
      simpa [hL] using hcong
    set c : ι → ℝ := fun i => ∑ j, W i j * v j with hc
    set S : Finset ι := univ.filter (fun i => c i ≠ 0) with hS
    have hneg : ∀ i ∈ S, preAct W b x i < 0 := by
      intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hrow : ∃ j, W i j ≠ 0 := by
        by_contra hrow
        push_neg at hrow
        exact hi (by simp [hc, hrow])
      have hne : preAct W b x i ≠ 0 := by
        rcases hx i with h | h
        · obtain ⟨j, hj⟩ := hrow
          exact absurd (h j) hj
        · exact h
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · refine absurd (hvA i ?_) hi
        simp [hA, ActiveRows, Finset.mem_filter, h, hrow]
    obtain ⟨t, ht0, ht⟩ := exists_pos_scale S (preAct W b x) c hneg
    have hlayer : reluLayer W b (x + t • v) = reluLayer W b x := by
      funext i
      by_cases hci : c i = 0
      · have hci' : (∑ j, W i j * v j) = 0 := hci
        simp [reluLayer, preAct_add_smul, hci']
      · have hiS : i ∈ S := by simp [hS, hci]
        have h1 : preAct W b x i < 0 := hneg i hiS
        have h2 : preAct W b x i + t * c i ≤ 0 := ht i hiS
        simp only [reluLayer, preAct_add_smul]
        rw [relu_of_nonpos h2, relu_of_nonpos h1.le]
    have hxx : x + t • v = x := hinj hlayer
    have htv : t • v = 0 := by
      nth_rewrite 2 [← add_zero x] at hxx
      exact add_left_cancel hxx
    rcases smul_eq_zero.mp htv with h | h
    · exact absurd h (ne_of_gt ht0)
    · exact h
  have hLinj : Function.Injective L := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  have h1 : Module.finrank ℝ (Fin n → ℝ) ≤ Module.finrank ℝ ({i // i ∈ A} → ℝ) :=
    LinearMap.finrank_le_finrank_of_injective hLinj
  rwa [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
