-- Prove2me | solution 1 for HyperAwareness11D.exists_antipodal_probes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:13:24.578285+00:00
-- url     : https://prove2.me/submissions/ac30ffc9-8364-4caf-af48-a2df806f10c8

-- Sol generated from MachineLearning/HyperAwareness11D/Injectivity.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_card_activeRows_ge
import Theorems.Thm_HyperAwareness11D_exists_generic_direction
import Theorems.Thm_HyperAwareness11D_exists_large_scale

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





lemma preAct_smul (W : ι → Fin n → ℝ) (b : ι → ℝ) (u : Fin n → ℝ) (s : ℝ) (i : ι) :
    preAct W b (s • u) i = s * (∑ j, W i j * u j) + b i := by
  have hj : ∀ j, W i j * (s * u j) = s * (W i j * u j) := fun j => by ring
  simp only [preAct, Pi.smul_apply, smul_eq_mul, hj, ← Finset.mul_sum]

/-! ## Two elementary scaling lemmas -/



/-! ## Genericity: a direction transverse to every nonzero row -/


/-! ## The local rank bound -/


/-! ## The sharp lower bound `width ≥ 2n` -/





/-! ## The matching construction: the positive/negative split layer -/










open HyperAwareness11D in
theorem solution[Fintype ι] (W : ι → Fin n → ℝ) (b : ι → ℝ)
    (hinj : Function.Injective (reluLayer W b)) :
    ∃ x y : Fin n → ℝ, n ≤ (ActiveRows W b x).card ∧ n ≤ (ActiveRows W b y).card ∧
      Disjoint (ActiveRows W b x) (ActiveRows W b y) := by
  classical
  obtain ⟨u, hu⟩ := exists_generic_direction W
  set d : ι → ℝ := fun i => ∑ j, W i j * u j with hd
  obtain ⟨s, hs0, hs⟩ := exists_large_scale d b
  have hpre : ∀ (σ : ℝ) (i : ι), preAct W b (σ • u) i = σ * d i + b i := by
    intro σ i; rw [preAct_smul]
  have hgen : ∀ σ : ℝ, |σ| = s → ∀ i, (∀ j, W i j = 0) ∨ preAct W b (σ • u) i ≠ 0 := by
    intro σ hσ i
    by_cases hrow : ∀ j, W i j = 0
    · exact Or.inl hrow
    · right
      push_neg at hrow
      have hdi : d i ≠ 0 := hu i hrow
      have hbi : |b i| < s * |d i| := hs i hdi
      rw [hpre]
      intro hzero
      have habs : |σ * d i| = s * |d i| := by rw [abs_mul, hσ]
      have hb : b i = -(σ * d i) := by linarith
      rw [hb, abs_neg, habs] at hbi
      exact lt_irrefl _ hbi
  have hplus := card_activeRows_ge W b hinj (s • u) (hgen s (abs_of_pos hs0))
  have hminus := card_activeRows_ge W b hinj ((-s) • u)
    (hgen (-s) (by rw [abs_neg, abs_of_pos hs0]))
  have hdisj : Disjoint (ActiveRows W b (s • u)) (ActiveRows W b ((-s) • u)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [ActiveRows, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    obtain ⟨hp, hrow⟩ := hi
    obtain ⟨hm, -⟩ := hi'
    rw [hpre] at hp hm
    have hdi : d i ≠ 0 := hu i hrow
    have hbi : |b i| < s * |d i| := hs i hdi
    have h1 : |b i| < |s * d i| := by rwa [abs_mul, abs_of_pos hs0]
    rcases abs_lt.mp h1 with ⟨hlow, hhigh⟩
    rcases le_or_gt 0 (s * d i) with h | h
    · rw [abs_of_nonneg h] at hhigh
      nlinarith
    · rw [abs_of_neg h] at hhigh
      nlinarith
  exact ⟨s • u, (-s) • u, hplus, hminus, hdisj⟩
