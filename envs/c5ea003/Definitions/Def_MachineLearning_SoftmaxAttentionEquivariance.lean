-- Prove2me | Definitions.Def_MachineLearning_SoftmaxAttentionEquivariance
-- name    : MachineLearning_SoftmaxAttentionEquivariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:59:55.497975+00:00
-- url     : https://prove2.me/theorems/fa79c76a-d459-4d89-b4f7-ec31de92f88a
-- title:
--   Aether Catalog definitions — MachineLearning_SoftmaxAttentionEquivariance
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SoftmaxAttentionEquivariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SoftmaxAttentionEquivariance.lean by skeleton subtraction
import Mathlib

/-!
# Permutation equivariance of scaled dot-product attention

This file formalizes standard row-wise softmax attention
`A(Q,K,V) = softmax(QKᵀ / √d) V` on finite token and feature types.
Its main theorem proves exact equivariance under an arbitrary simultaneous permutation
of the query, key, and value token axes.  Further results establish positivity,
row-stochasticity, preservation of constant values, and closure under stacking.
-/

open scoped BigOperators

namespace SoftmaxAttention

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ]

/-- Scaled dot-product score.  The positive parameter `scale` represents `√d`. -/
noncomputable def scaledScore (scale : ℝ) (q k : κ → ℝ) : ℝ :=
  (∑ a, q a * k a) / scale

/-- The normalizing denominator in one row of softmax attention. -/
noncomputable def softmaxDenom (scale : ℝ) (q : ι → κ → ℝ) (k : ι → κ → ℝ) (i : ι) : ℝ :=
  ∑ j, Real.exp (scaledScore scale (q i) (k j))

/-- A row-wise softmax attention weight. -/
noncomputable def softmaxWeight (scale : ℝ) (q : ι → κ → ℝ) (k : ι → κ → ℝ)
    (i j : ι) : ℝ :=
  Real.exp (scaledScore scale (q i) (k j)) / softmaxDenom scale q k i

/-- Standard scaled dot-product attention applied to a value tensor. -/
noncomputable def attention (scale : ℝ) (q : ι → κ → ℝ) (k : ι → κ → ℝ)
    (v : ι → ν → ℝ) (i : ι) (b : ν) : ℝ :=
  ∑ j, softmaxWeight scale q k i j * v j b

/-- Reindex a token-indexed tensor by a permutation. -/
def permute (σ : Equiv.Perm ι) (x : ι → κ → ℝ) : ι → κ → ℝ :=
  fun i => x (σ.symm i)








end SoftmaxAttention


