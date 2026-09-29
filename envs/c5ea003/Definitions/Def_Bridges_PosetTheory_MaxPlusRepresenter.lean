-- Prove2me | Definitions.Def_Bridges_PosetTheory_MaxPlusRepresenter
-- name    : Bridges_PosetTheory_MaxPlusRepresenter
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:03.350866+00:00
-- url     : https://prove2.me/theorems/40cc221d-dbf1-4f6f-a6e3-8bdd6d8c02dc
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_MaxPlusRepresenter
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.MaxPlusRepresenter`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/MaxPlusRepresenter.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Max-Plus Representer Theorem for Idempotent Kernel Regression

This file formalizes the idempotent representer theorem for max-plus kernel regression.
The main result states that whenever a projection-to-span operator exists that preserves
training values and does not increase regularization, every minimizer of a regularized
empirical risk can be replaced by one in the tropical kernel span — with the same objective
value.

This is the idempotent/tropical analogue of the classical RKHS representer theorem:
instead of Hilbert-space orthogonal projection, the key mechanism is order-theoretic
residuation. The finite case formalized here already captures the full algorithmic content:
infinite-dimensional optimization over functions collapses to finite coefficient optimization
over the training set.

## Main results

* `representer_theorem_of_projection`: any minimizer admits a span-supported minimizer
  with the same objective value, given a suitable projection.
* `exists_span_minimizer_of_exists_minimizer`: the stronger corollary that a global
  minimizer exists in the kernel span whenever one exists at all.
* `representerProjOfInterp_is_projection`: a concrete projection built from training
  interpolation.
* `optimization_reduces_to_coefficients`: the algorithmic reduction from function-space
  optimization to finite coefficient-space optimization.
* `exists_kernel_span_interpolant_of_trainKronecker`: exact interpolation for Kronecker
  tropical kernels.

## Mathematical context

In the max-plus semiring (ℝ ∪ {-∞}, max, +):
- **Tropical addition** is `max` (i.e., `⊔` in lattice notation)
- **Tropical multiplication** is classical `+`

The tropical span of kernel sections uses tropical multiplication (`+`) to combine
kernel values with coefficients, and tropical addition (`sup`) to aggregate over
the training set:
  `f(z) = ⊕_{x ∈ train} K(z,x) ⊗ c(x) = sup_{x ∈ train} (K(z,x) + c(x))`

## References

* Litvinov, Maslov, Shpiz — "Idempotent functional analysis: an algebraic approach"
* Cohen, Gaubert, Quadrat — "Duality and separation theorems in idempotent semimodules"
* Singer — "Abstract Convex Analysis"
-/


open scoped BigOperators

variable {X Y α : Type*}

/-! ## Tropical span and kernel sections -/


/-- The tropical span of kernel sections over a training set.
A function `f` lies in the span if it can be written as
`f(z) = sup_{x ∈ train} (K(z,x) + c(x))` for some coefficients `c`.
Here `+` is the tropical multiplication (classical addition in max-plus)
and `sup` is the tropical summation (max). -/
def tropicalSpanOn
    [SemilatticeSup α] [OrderBot α] [Add α]
    (K : X → X → α) (train : Finset X) : Set (X → α) :=
  {f | ∃ c : X → α,
      f = fun z => train.sup fun x => K z x + c x}

/-! ## Empirical risk and objective -/

/-- Empirical risk: the supremum of pointwise losses over the training set. -/
def empiricalRisk
    [SemilatticeSup α] [OrderBot α]
    (train : Finset X) (loss : X → α → Y → α) (y : X → Y) (f : X → α) : α :=
  train.sup fun x => loss x (f x) (y x)

/-- The regularized objective: supremum of empirical risk and regularization.
In the max-plus semiring, addition is `⊔`, so this is the "sum" of the two terms. -/
def objective
    [SemilatticeSup α] [OrderBot α]
    (train : Finset X) (loss : X → α → Y → α) (y : X → Y)
    (reg : (X → α) → α) (f : X → α) : α :=
  (empiricalRisk train loss y f) ⊔ (reg f)

/-! ## Representer projection -/

/-- A function `P` is a representer projection if:
1. It maps every function into the tropical kernel span.
2. It preserves function values on the training set.
3. It does not increase the regularizer. -/
def IsRepresenterProjection
    [SemilatticeSup α] [OrderBot α] [Add α]
    (K : X → X → α) (train : Finset X) (reg : (X → α) → α)
    (P : (X → α) → (X → α)) : Prop :=
  (∀ f, P f ∈ tropicalSpanOn K train) ∧
  (∀ f x, x ∈ train → P f x = f x) ∧
  (∀ f, reg (P f) ≤ reg f)

/-! ## Helper lemmas -/





/-! ## Main representer theorem -/



/-! ## Training interpolation and concrete projection -/

/-- A kernel has training interpolation if every function's values on the training set
can be exactly reproduced by some element of the tropical kernel span. -/
def HasTrainInterpolation
    [SemilatticeSup α] [OrderBot α] [Add α]
    (K : X → X → α) (train : Finset X) : Prop :=
  ∀ f : X → α, ∃ c : X → α,
    ∀ x, x ∈ train →
      (train.sup fun z => K x z + c z) = f x

/-- Concrete projection: given training interpolation, project any function
to a span element that agrees on the training set. Uses classical choice. -/
noncomputable def representerProjOfInterp
    [SemilatticeSup α] [OrderBot α] [Add α]
    (K : X → X → α) (train : Finset X)
    (hinterp : HasTrainInterpolation K train)
    (f : X → α) : X → α :=
  fun z => train.sup fun x => K z x + (hinterp f).choose x


/-! ## Kronecker tropical kernel -/

/-- A kernel is train-Kronecker if it has zero diagonal entries (identity for tropical
multiplication) on the training set and bottom (absorbing element, i.e., tropical zero)
off-diagonal entries within the training set.

In the max-plus semiring (ℝ ∪ {-∞}, max, +), the identity for `+` is `0` and the
absorbing element is `-∞` (= ⊥). A Kronecker kernel has `K(x,x) = 0` on diagonal
and `K(z,x) = -∞` off diagonal. -/
def IsTrainKroneckerKernel
    [Preorder α] [OrderBot α] [Add α] [Zero α]
    (K : X → X → α) (train : Finset X) : Prop :=
  (∀ x, x ∈ train → K x x = 0) ∧
  (∀ x z, x ∈ train → z ∈ train → x ≠ z → K z x = ⊥)

/-
For a Kronecker tropical kernel over a type with absorbing ⊥ and additive identity 0,
every function can be interpolated exactly on the training set by an element of the
tropical kernel span.

The key insight: set `c(x) = f(x)` for all `x`. Then at training point `x₀`:
- The `x₀` term contributes `K(x₀,x₀) + f(x₀) = 0 + f(x₀) = f(x₀)`
- Every other term `x ≠ x₀` contributes `K(x₀,x) + f(x) = ⊥ + f(x) = ⊥`
- So the sup equals `f(x₀)`.
-/

/-! ## Coefficient-space objective and algorithmic reduction -/

/-- The coefficient-space objective: the regularized empirical risk as a function
of the coefficient vector `c`, with the function reconstructed from the kernel span. -/
def coeffObjective
    [SemilatticeSup α] [OrderBot α] [Add α]
    (K : X → X → α) (train : Finset X) (y : X → Y)
    (loss : X → α → Y → α) (reg : (X → α) → α) (c : X → α) : α :=
  let f : X → α := fun z => train.sup fun x => K z x + c x
  objective train loss y reg f


