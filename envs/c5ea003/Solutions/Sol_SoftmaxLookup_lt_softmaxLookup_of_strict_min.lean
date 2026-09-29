-- Prove2me | solution 1 for SoftmaxLookup.lt_softmaxLookup_of_strict_min
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T00:39:24.470965+00:00
-- url     : https://prove2.me/submissions/01c69e5d-4f8a-4b21-a6cf-d0b71eebac22

-- Sol generated from MachineLearning/TransformerUniversality/SoftmaxLookup.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxLookup

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


omit [DecidableEq ι] in
/-- The softmax partition function is strictly positive. -/
theorem denom_pos [Nonempty ι] (beta : ℝ) (s : ι → ℝ) :
    0 < ∑ k, Real.exp (beta * s k) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [DecidableEq ι] in
/-- Softmax weights are strictly positive. -/
theorem weight_pos [Nonempty ι] (beta : ℝ) (s : ι → ℝ) (j : ι) :
    0 < weight beta s j :=
  div_pos (Real.exp_pos _) (denom_pos beta s)

omit [DecidableEq ι] in
/-- Softmax weights sum to one. -/
theorem sum_weight [Nonempty ι] (beta : ℝ) (s : ι → ℝ) :
    ∑ j, weight beta s j = 1 := by
  simp only [weight]
  rw [← Finset.sum_div, div_self (ne_of_gt (denom_pos beta s))]






variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]





variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]











open SoftmaxLookup in
theorem solution(hcard : 2 ≤ Fintype.card X) (beta : ℝ)
    (f : X → ℝ) (x : X) (hmin : ∀ a, a ≠ x → f x < f a) :
    f x < softmaxLookup beta f x := by
  classical
  have hsum : softmaxLookup beta f x - f x
      = ∑ a ∈ Finset.univ.erase x,
          weight beta (fun a => ∑ i, oneHot x i * oneHot a i) a * (f a - f x) := by
    have hw : ∑ a, weight beta (fun a => ∑ i, oneHot x i * oneHot a i) a = 1 :=
      sum_weight _ _
    have hsplit : ∑ a, weight beta (fun a => ∑ i, oneHot x i * oneHot a i) a * (f a - f x)
        = softmaxLookup beta f x - f x := by
      simp only [mul_sub, Finset.sum_sub_distrib, softmaxLookup, softmaxRead,
        ← Finset.sum_mul, hw, one_mul]
    rw [← hsplit, ← Finset.add_sum_erase Finset.univ
      (fun a => weight beta (fun a => ∑ i, oneHot x i * oneHot a i) a * (f a - f x))
      (Finset.mem_univ x)]
    simp
  have hpos : 0 < ∑ a ∈ Finset.univ.erase x,
      weight beta (fun a => ∑ i, oneHot x i * oneHot a i) a * (f a - f x) := by
    apply Finset.sum_pos
    · intro a ha
      have hne : a ≠ x := Finset.ne_of_mem_erase ha
      exact mul_pos (weight_pos _ _ a) (by linarith [hmin a hne])
    · obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hcard
      by_cases h : a = x
      · exact ⟨b, Finset.mem_erase.mpr ⟨fun hb => hab (by rw [h, hb]), Finset.mem_univ b⟩⟩
      · exact ⟨a, Finset.mem_erase.mpr ⟨h, Finset.mem_univ a⟩⟩
  linarith [hsum, hpos]
