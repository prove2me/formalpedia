-- Prove2me | solution 1 for HyperAwareness11D.exists_pos_scale
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:08:57.286397+00:00
-- url     : https://prove2.me/submissions/39da70aa-7b96-4e2e-b7fe-056f06b5d385

-- Sol generated from MachineLearning/HyperAwareness11D/Injectivity.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity

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






/-! ## Two elementary scaling lemmas -/



/-! ## Genericity: a direction transverse to every nonzero row -/


/-! ## The local rank bound -/


/-! ## The sharp lower bound `width ≥ 2n` -/





/-! ## The matching construction: the positive/negative split layer -/










open HyperAwareness11D in
theorem solution{α : Type*} (S : Finset α) (p c : α → ℝ) (h : ∀ i ∈ S, p i < 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ∈ S, p i + t * c i ≤ 0 := by
  by_cases hS : S.Nonempty
  · have ht0 : 0 < S.inf' hS (fun i => -p i / (1 + |c i|)) := by
      rw [Finset.lt_inf'_iff]
      intro k hk
      have h1' : (0:ℝ) < 1 + |c k| := by positivity
      exact div_pos (by linarith [h k hk]) h1'
    refine ⟨S.inf' hS (fun i => -p i / (1 + |c i|)), ht0, ?_⟩
    intro i hi
    have h1 : (0:ℝ) < 1 + |c i| := by positivity
    have hle : S.inf' hS (fun i => -p i / (1 + |c i|)) ≤ -p i / (1 + |c i|) :=
      Finset.inf'_le _ hi
    have hmul : S.inf' hS (fun i => -p i / (1 + |c i|)) * (1 + |c i|) ≤ -p i := by
      rw [← le_div_iff₀ h1]
      exact hle
    have habs : c i ≤ |c i| := le_abs_self _
    nlinarith [ht0]
  · exact ⟨1, one_pos, fun i hi => absurd ⟨i, hi⟩ hS⟩
