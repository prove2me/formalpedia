-- Prove2me | Theorems.Thm_SoftmaxLookup_sum_weight_erase_le
-- name    : SoftmaxLookup.sum_weight_erase_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:53:25.385979+00:00
-- url     : https://prove2.me/theorems/0d66a2fc-b83c-4f13-9060-28edd7688dfc
-- title:
--   Exponential concentration of softmax on a separated argmax.
-- statement:
--   **Exponential concentration of softmax on a separated argmax.**
--   If every competing index is below `s i₀` by at least `γ`, the total off-argmax softmax mass
--   is at most `(n-1) * exp (-(β*γ))`.
--
--   ```lean
--   theorem SoftmaxLookup.sum_weight_erase_le(beta gamma : ℝ) (s : ι → ℝ) (i₀ : ι)
--       (hbeta : 0 ≤ beta) (hgap : ∀ j, j ≠ i₀ → s j + gamma ≤ s i₀) :
--       ∑ j ∈ Finset.univ.erase i₀, weight beta s j
--         ≤ (Fintype.card ι - 1 : ℝ) * Real.exp (-(beta * gamma)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/SoftmaxLookup.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/SoftmaxLookup.lean#L70

-- Thm stub generated from MachineLearning/TransformerUniversality/SoftmaxLookup.lean
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

theorem SoftmaxLookup.sum_weight_erase_le(beta gamma : ℝ) (s : ι → ℝ) (i₀ : ι)
    (hbeta : 0 ≤ beta) (hgap : ∀ j, j ≠ i₀ → s j + gamma ≤ s i₀) :
    ∑ j ∈ Finset.univ.erase i₀, weight beta s j
      ≤ (Fintype.card ι - 1 : ℝ) * Real.exp (-(beta * gamma)) := by sorry
