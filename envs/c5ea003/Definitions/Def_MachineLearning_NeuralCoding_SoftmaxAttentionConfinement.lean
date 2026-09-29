-- Prove2me | Definitions.Def_MachineLearning_NeuralCoding_SoftmaxAttentionConfinement
-- name    : MachineLearning_NeuralCoding_SoftmaxAttentionConfinement
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:41.968684+00:00
-- url     : https://prove2.me/theorems/1063751c-bc6e-4a21-b669-39af65a577e6
-- title:
--   Aether Catalog definitions — MachineLearning_NeuralCoding_SoftmaxAttentionConfinement
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NeuralCoding.SoftmaxAttentionConfinement`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NeuralCoding/SoftmaxAttentionConfinement.lean by skeleton subtraction
import Mathlib
/-
  Softmax Attention Convex-Hull Confinement
  =========================================

  This file formalizes the basic "convex-hull confinement" property of a single
  softmax self-attention head: the output of attention is a convex combination
  of the value vectors, hence it is confined to the coordinate-wise interval
  (and thus the convex hull) spanned by the values.

  We model an attention head with:
  * a query vector `q : Fin d → ℝ`,
  * key vectors `ks : Fin n → Fin d → ℝ` (one key per token),
  * value vectors `vs : Fin n → Fin m → ℝ` (one value per token).

  The unnormalized score (kernel) of a key is `expKernel q k = exp ⟪q, k⟫`,
  the partition function `attnPartition` is the sum of the kernels, the
  attention weights `attnWeight` are the normalized kernels (a probability
  distribution over tokens), and the output `attnOutput` is the weighted
  average of the values.

  Main results:
  * `attnWeight_sum_one`     : the attention weights sum to one.
  * `convexCombo_mem_Icc`    : a convex combination stays in any interval
                               containing the points.
  * `attnOutput_mem_Icc`     : each output coordinate is confined to the
                               interval spanned by the value coordinates.
  * `logPartition_ge_term`   : the log-partition dominates every individual
                               score (a log-sum-exp lower bound).
-/


open Finset
open scoped BigOperators

noncomputable section

variable {d n m : ℕ}

/-- Unnormalized exponential kernel (score) of a key relative to a query:
`exp ⟪q, k⟫`. -/
def expKernel (q : Fin d → ℝ) (k : Fin d → ℝ) : ℝ :=
  Real.exp (∑ i, q i * k i)

/-- The softmax partition function: the sum of the kernels over all tokens. -/
def attnPartition (q : Fin d → ℝ) (ks : Fin n → Fin d → ℝ) : ℝ :=
  ∑ j, expKernel q (ks j)

/-- The softmax attention weight assigned to token `j`. -/
def attnWeight (q : Fin d → ℝ) (ks : Fin n → Fin d → ℝ) (j : Fin n) : ℝ :=
  expKernel q (ks j) / attnPartition q ks

/-- The attention output's `i`-th coordinate: the weighted average of the
`i`-th coordinate of each value vector. -/
def attnOutput (q : Fin d → ℝ) (ks : Fin n → Fin d → ℝ)
    (vs : Fin n → Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j, attnWeight q ks j * vs j i

/-! ### Basic positivity lemmas -/





/-! ### The four main theorems -/

/-
The softmax attention weights form a probability distribution: they sum to
one.
-/

/-
A convex combination of points lying in an interval `Icc lo hi` again lies
in `Icc lo hi`.
-/

/-
Convex-hull confinement: each output coordinate is confined to the interval
`Icc lo hi` spanned by the corresponding value coordinates.
-/

/-
The log-partition function dominates each individual score: a log-sum-exp
lower bound.
-/

end


