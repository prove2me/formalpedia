-- Prove2me | Definitions.Def_MachineLearning_Attention
-- name    : MachineLearning_Attention
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:36:57.280784+00:00
-- url     : https://prove2.me/theorems/ce3f0da8-183e-44e1-98f9-50ba2f87fadc
-- title:
--   Aether Catalog definitions — MachineLearning_Attention
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.Attention`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/Attention.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Categorical Neural Architecture Theory. All rights reserved.
Released under Apache 2.0 license.

# Attention as a Natural Transformation

This file proves that linear attention mechanisms satisfy the naturality condition
from category theory. Specifically, scalar attention (attention weights proportional
to identity) commutes with all linear maps, making it a natural endomorphism of the
identity functor on the category of finite-dimensional vector spaces.

## Main results

* `scalar_attention_natural_component` — scalar attention commutes with linear maps
* `scalar_attention_natural_matrix` — matrix form of naturality
* `attention_natural_iff_scalar` — attention is natural iff it is scalar (Schur's lemma)
* `attention_composed_natural` — composition of natural attentions is natural
-/


open Matrix BigOperators

variable {n m : ℕ}

/-! ## Linear Attention Operators -/

/-- Apply a linear attention operator (given as a matrix) to a state vector. -/
def attApply (W : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ := W.mulVec x

/-- Scalar attention: attention weight is a scalar multiple of identity.
    This models uniform attention where every position receives equal weight `c`. -/
def scalarAttention (n : ℕ) (c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  c • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The action of a linear map on state vectors (functor action on morphisms). -/
def linearAction (φ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  φ.mulVec x

/-! ## Naturality Theorems -/

/-
**Theorem 2a (Scalar Attention Naturality — Component Form).**
    For any linear map φ and scalar attention weight c,
    applying φ after attention equals applying attention after φ.
    This is the naturality square: `φ ∘ att_n = att_m ∘ φ`.
-/

/-
**Theorem 2b (Scalar Attention Naturality — Matrix Form).**
    φ * (c • I) = (c • I) * φ as square matrices.
-/

/-
**Theorem 2c (Natural Attention Characterization).**
    An attention operator commutes with ALL endomorphisms
    if and only if it is a scalar multiple of identity.
    This is the Schur lemma for the matrix algebra.
-/

/-
**Theorem 2d (Composed Natural Attentions).**
    If two operators both commute with all morphisms, their product does too.
    Natural transformations form a monoid.
-/

/-
Natural attention operators form a subalgebra (closed under addition).
-/

/-
Scalar attention applied to a vector scales it uniformly.
-/

/-
Scalar attention at c=1 is the identity matrix.
-/

/-
Scalar attention at c=0 is the zero matrix.
-/


