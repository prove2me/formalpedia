-- Prove2me | solution 1 for SoftmaxLookup.abs_softmaxRead_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T00:39:23.963761+00:00
-- url     : https://prove2.me/submissions/a49df36f-478d-426b-bc8d-ff0b76cbd046

-- Sol generated from MachineLearning/TransformerUniversality/SoftmaxLookup.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxLookup
import Theorems.Thm_SoftmaxLookup_sum_weight_erase_le

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
theorem solution(beta gamma M : ℝ) (s v : ι → ℝ) (i₀ : ι)
    (hbeta : 0 ≤ beta) (hgap : ∀ j, j ≠ i₀ → s j + gamma ≤ s i₀)
    (hv : ∀ j, |v j| ≤ M) :
    |softmaxRead beta s v - v i₀|
      ≤ 2 * M * (Fintype.card ι - 1 : ℝ) * Real.exp (-(beta * gamma)) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (v i₀)) (hv i₀)
  have hkey : softmaxRead beta s v - v i₀
      = ∑ j ∈ Finset.univ.erase i₀, weight beta s j * (v j - v i₀) := by
    have hsum : ∑ j, weight beta s j * (v j - v i₀)
        = softmaxRead beta s v - v i₀ := by
      simp only [mul_sub, Finset.sum_sub_distrib, softmaxRead, ← Finset.sum_mul,
        sum_weight beta s, one_mul]
    rw [← hsum, ← Finset.add_sum_erase Finset.univ
      (fun j => weight beta s j * (v j - v i₀)) (Finset.mem_univ i₀)]
    simp
  rw [hkey]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ j ∈ Finset.univ.erase i₀,
      |weight beta s j * (v j - v i₀)| ≤ (2 * M) * weight beta s j := by
    intro j _
    rw [abs_mul, abs_of_pos (weight_pos beta s j), mul_comm]
    have hdiff : |v j - v i₀| ≤ 2 * M := by
      have h1 := hv j
      have h2 := hv i₀
      calc |v j - v i₀| ≤ |v j| + |v i₀| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    exact mul_le_mul_of_nonneg_right hdiff (le_of_lt (weight_pos beta s j))
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [← Finset.mul_sum]
  have hmass := sum_weight_erase_le beta gamma s i₀ hbeta hgap
  calc (2 * M) * ∑ j ∈ Finset.univ.erase i₀, weight beta s j
      ≤ (2 * M) * ((Fintype.card ι - 1 : ℝ) * Real.exp (-(beta * gamma))) :=
        mul_le_mul_of_nonneg_left hmass (by linarith)
    _ = 2 * M * (Fintype.card ι - 1 : ℝ) * Real.exp (-(beta * gamma)) := by ring
