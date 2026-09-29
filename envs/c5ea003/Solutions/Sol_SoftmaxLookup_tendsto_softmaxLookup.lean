-- Prove2me | solution 1 for SoftmaxLookup.tendsto_softmaxLookup
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T01:12:26.662318+00:00
-- url     : https://prove2.me/submissions/0e4c0f0e-8919-49cc-863e-901ce2f088db

-- Sol generated from MachineLearning/TransformerUniversality/SoftmaxLookup.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxLookup
import Theorems.Thm_SoftmaxLookup_softmaxLookup_eps_approximation

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











open SoftmaxLookup in
theorem solution(f : X → ℝ) (x : X) :
    Filter.Tendsto (fun beta : ℝ => softmaxLookup beta f x) Filter.atTop (nhds (f x)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨M, hM⟩ : ∃ M, ∀ a, |f a| ≤ M := by
    refine ⟨(Finset.univ.sup' Finset.univ_nonempty (fun a => |f a|)), fun a => ?_⟩
    exact Finset.le_sup' (fun a => |f a|) (Finset.mem_univ a)
  refine ⟨max 0 (Real.log ((2 * M * (Fintype.card X - 1 : ℝ) + 1) / eps)), fun beta hb => ?_⟩
  have hb0 : 0 ≤ beta := le_trans (le_max_left _ _) hb
  have hb1 : Real.log ((2 * M * (Fintype.card X - 1 : ℝ) + 1) / eps) ≤ beta :=
    le_trans (le_max_right _ _) hb
  have := softmaxLookup_eps_approximation M eps f heps hM beta hb1 hb0 x
  rwa [Real.dist_eq]
