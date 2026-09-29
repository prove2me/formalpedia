-- Prove2me | Definitions.Def_MachineLearning_TransformerArchitecture
-- name    : MachineLearning_TransformerArchitecture
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:14.901667+00:00
-- url     : https://prove2.me/theorems/3f152cc0-b384-4a45-9286-5122ab9a3050
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerArchitecture
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerArchitecture`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerArchitecture.lean by skeleton subtraction
import Mathlib

/-!
# A finite mathematical model of transformer architecture

This file develops three elementary components of a transformer and culminates in an
exact finite universality theorem.  The attention model is *linear attention* (no
softmax): its score is a bilinear form and its heads are summed.  The universality
statement concerns functions on a finite set of fixed-length discrete sequences.  It
is therefore an exact lookup-table theorem, not a claim about standard softmax
transformers on arbitrary Euclidean compacta.
-/

open scoped BigOperators

namespace TransformerArchitecture

section BilinearAttention

variable {ι : Type*} [Fintype ι]

/-- A matrix-parametrized attention score, bilinear in its query and key. -/
def bilinearScore (W : Matrix ι ι ℝ) (q k : ι → ℝ) : ℝ :=
  ∑ i, q i * (W.mulVec k) i






end BilinearAttention

section PositionalAndNormalization

variable {ι : Type*}

/-- Additive positional encoding. -/
def positionalEncoding (position content : ι → ℝ) : ι → ℝ :=
  content + position


/-- The affine part of layer normalization, with coordinatewise scale and bias.

The data-dependent centering and variance normalization of standard layer
normalization is deliberately not called affine; this definition isolates its learned
affine post-transformation. -/
def affineNorm (scale bias x : ι → ℝ) : ι → ℝ :=
  fun i => scale i * x i + bias i



end PositionalAndNormalization

section FiniteUniversality

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- One-hot embedding of a finite token or an entire finite sequence. -/
def oneHot (x : X) : X → ℝ :=
  fun y => if y = x then 1 else 0




/-- A head has a fixed key `a` and emits its value weighted by bilinear attention. -/
def lookupHead (f : X → Y → ℝ) (a x : X) : Y → ℝ :=
  fun y => (∑ i, oneHot x i * oneHot a i) * f a y


/-- Multi-head attention uses one lookup head for every possible input. -/
def multiHeadLookup (f : X → Y → ℝ) (x : X) : Y → ℝ :=
  ∑ a, lookupHead f a x




end FiniteUniversality

end TransformerArchitecture


