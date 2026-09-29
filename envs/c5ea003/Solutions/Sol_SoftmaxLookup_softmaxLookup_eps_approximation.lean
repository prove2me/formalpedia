-- Prove2me | solution 1 for SoftmaxLookup.softmaxLookup_eps_approximation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T00:55:40.784655+00:00
-- url     : https://prove2.me/submissions/9f502040-4625-4f1f-84a4-f9a47f14d0f5

-- Sol generated from MachineLearning/TransformerUniversality/SoftmaxLookup.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxLookup
import Theorems.Thm_SoftmaxLookup_abs_softmaxRead_sub_le

/-!
# Quantitative convergence of softmax lookup heads to the exact finite selector

The catalog file `Catalog/MachineLearning/TransformerArchitecture.lean` proves an *exact*
finite universality theorem for a linear-attention lookup architecture: with one head per
possible input, `multiHeadLookup f x = f x` on the nose.  The attention there is a bilinear
score with no softmax, so the "selection" is exact by construction.

This file supplies the missing quantitative bridge to genuine softmax attention.  Writing
`β` for the inverse temperature (equivalently, the score scale), we prove:

* `sum_weight_erase_le` — the total softmax mass off a `γ`-separated argmax is at most
  `(n-1) * exp (-(β*γ))`;
* `abs_softmaxRead_sub_le` — hence a softmax read of a bounded value vector differs from
  the hard selection by at most `2*M*(n-1)*exp (-(β*γ))`;
* `softmaxLookup_error_le` — instantiated at one-hot keys, where the score gap is exactly
  `1`, this bounds the error of a *softmax* lookup head against the exact finite selector;
* `softmaxLookup_eps_approximation` — the resulting ε-approximation theorem with an
  **explicit** admissible score scale.

The scope qualification of the original development is preserved and in fact sharpened:
everything below is a statement about a *fixed finite* input set, with an error bound whose
constant grows linearly in the number of heads `n = |X|`.  It is not the continuous uniform
universal-approximation theorem for softmax transformers.
-/

open scoped BigOperators

open SoftmaxLookup


variable {ι : Type*} [Fintype ι] [DecidableEq ι]










variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]





variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]


omit [Nonempty X] in
/-- Dot-product attention between one-hot vectors is exact equality testing. -/
theorem oneHot_score (x a : X) :
    (∑ i, oneHot x i * oneHot a i) = if a = x then 1 else 0 := by
  by_cases h : a = x
  · subst h; simp [oneHot]
  · rw [if_neg h, Finset.sum_eq_zero]
    intro i _
    by_cases hi : i = x
    · subst hi
      simp [oneHot, Ne.symm h]
    · simp [oneHot, hi]


omit [Nonempty X] in
/-- The one-hot score has an exact unit gap at the matching key. -/
theorem oneHot_gap (x : X) :
    ∀ a, a ≠ x → (∑ i, oneHot x i * oneHot a i) + 1
      ≤ (∑ i, oneHot x i * oneHot x i) := by
  intro a ha
  rw [oneHot_score, oneHot_score, if_neg ha, if_pos rfl]
  norm_num

/-- **Softmax lookup converges to the exact finite selector, quantitatively.**
With one head per possible input and one-hot keys, the softmax read at score scale `β`
reproduces the exact lookup value `f x` up to `2*M*(|X|-1)*exp (-β)`. -/
theorem softmaxLookup_error_le (beta M : ℝ) (f : X → ℝ) (x : X)
    (hbeta : 0 ≤ beta) (hf : ∀ a, |f a| ≤ M) :
    |softmaxLookup beta f x - f x|
      ≤ 2 * M * (Fintype.card X - 1 : ℝ) * Real.exp (-beta) := by
  have h := abs_softmaxRead_sub_le (ι := X) beta 1 M
    (fun a => ∑ i, oneHot x i * oneHot a i) f x hbeta (oneHot_gap x) hf
  simpa using h






open SoftmaxLookup in
theorem solution(M eps : ℝ) (f : X → ℝ)
    (heps : 0 < eps) (hf : ∀ a, |f a| ≤ M) :
    ∀ beta, Real.log ((2 * M * (Fintype.card X - 1 : ℝ) + 1) / eps) ≤ beta → 0 ≤ beta →
      ∀ x, |softmaxLookup beta f x - f x| < eps := by
  intro beta hbeta hbeta0 x
  have hM : 0 ≤ M := le_trans (abs_nonneg (f x)) (hf x)
  set C : ℝ := 2 * M * (Fintype.card X - 1 : ℝ) with hC
  have hcard : (1:ℝ) ≤ (Fintype.card X : ℝ) := by
    have h : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast h
  have hCnonneg : 0 ≤ C := by rw [hC]; nlinarith
  have hpos : (0:ℝ) < C + 1 := by linarith
  have hquot : 0 < (C + 1) / eps := by positivity
  have hexp : Real.exp (-beta) ≤ eps / (C + 1) := by
    have h1 : Real.exp (-beta) ≤ Real.exp (-Real.log ((C + 1) / eps)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log ((C + 1) / eps)) = eps / (C + 1) := by
      rw [Real.exp_neg, Real.exp_log hquot, inv_div]
    rw [h2] at h1
    exact h1
  have hmain := softmaxLookup_error_le beta M f x hbeta0 hf
  calc |softmaxLookup beta f x - f x| ≤ C * Real.exp (-beta) := hmain
    _ ≤ C * (eps / (C + 1)) := mul_le_mul_of_nonneg_left hexp hCnonneg
    _ < eps := by
        rw [mul_div_assoc', div_lt_iff₀ hpos]
        nlinarith
