-- Prove2me | solution 1 for HyperAwareness11D.doubleLayer_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:17:17.088741+00:00
-- url     : https://prove2.me/submissions/3a563540-291a-4461-9268-9bc22aa1823a

-- Sol generated from MachineLearning/HyperAwareness11D/Injectivity.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_preAct_doubleW_inl
import Theorems.Thm_HyperAwareness11D_preAct_doubleW_inr
import Theorems.Thm_HyperAwareness11D_relu_of_nonneg
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




/-- `relu t - relu (-t) = t`: the positive/negative split loses no information. -/
lemma relu_sub_relu_neg (t : ℝ) : relu t - relu (-t) = t := by
  rcases le_total t 0 with h | h
  · rw [relu_of_nonpos h, relu_of_nonneg (neg_nonneg.mpr h)]; ring
  · rw [relu_of_nonneg h, relu_of_nonpos (neg_nonpos.mpr h)]; ring

variable {ι ι' : Type*} {n : ℕ}






/-! ## Two elementary scaling lemmas -/



/-! ## Genericity: a direction transverse to every nonzero row -/


/-! ## The local rank bound -/


/-! ## The sharp lower bound `width ≥ 2n` -/





/-! ## The matching construction: the positive/negative split layer -/




/-- **Exact reconstruction.**  The `2n`-unit split layer admits a *linear* left inverse:
the input is recovered as the difference of the two halves.  No information is lost. -/
theorem doubleLayer_reconstruct (x : Fin n → ℝ) (i : Fin n) :
    reluLayer (doubleW n) 0 x (Sum.inl i) - reluLayer (doubleW n) 0 x (Sum.inr i) = x i := by
  simp only [reluLayer, preAct_doubleW_inl, preAct_doubleW_inr]
  exact relu_sub_relu_neg (x i)






open HyperAwareness11D in
theorem solution: Function.Injective (reluLayer (doubleW n) 0) := by
  intro x y hxy
  funext i
  rw [← doubleLayer_reconstruct x i, ← doubleLayer_reconstruct y i, hxy]
