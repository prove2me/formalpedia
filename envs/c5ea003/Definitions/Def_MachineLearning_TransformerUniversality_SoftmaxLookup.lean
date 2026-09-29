-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxLookup
-- name    : MachineLearning_TransformerUniversality_SoftmaxLookup
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:49.969308+00:00
-- url     : https://prove2.me/theorems/26b8eda8-b749-4953-8816-a160f5ffb5f1
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_SoftmaxLookup
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.SoftmaxLookup`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/SoftmaxLookup.lean by skeleton subtraction
import Mathlib

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

namespace SoftmaxLookup

section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Softmax weights at inverse temperature (score scale) `β` for a score vector `s`. -/
noncomputable def weight (beta : ℝ) (s : ι → ℝ) (j : ι) : ℝ :=
  Real.exp (beta * s j) / ∑ k, Real.exp (beta * s k)







end Weights

section Read

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A softmax attention read: the convex combination of values with softmax weights. -/
noncomputable def softmaxRead (beta : ℝ) (s : ι → ℝ) (v : ι → ℝ) : ℝ :=
  ∑ j, weight beta s j * v j


end Read

section OneHotLookup

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- One-hot embedding, as in the catalog transformer file. -/
def oneHot (x : X) : X → ℝ := fun y => if y = x then 1 else 0


/-- A **softmax** lookup head: soft attention at score scale `β` over one head per possible
input, reading the value table `f`. -/
noncomputable def softmaxLookup (beta : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  softmaxRead beta (fun a => ∑ i, oneHot x i * oneHot a i) f






end OneHotLookup

end SoftmaxLookup


