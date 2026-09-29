-- Prove2me | Theorems.Thm_productFamily_separatesPointsStrongly
-- name    : productFamily_separatesPointsStrongly
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:03.034667+00:00
-- url     : https://prove2.me/theorems/6c73320e-f1a6-4331-9048-57ae88401f88
-- title:
--   ProductFamily separatesPointsStrongly
-- statement:
--   Formal statement of `productFamily_separatesPointsStrongly` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem productFamily_separatesPointsStrongly    {A : Set C(X, ℝ)} {B : Set C(Y, ℝ)}
--       (hA_sep : ∀ x₁ x₂ : X, x₁ ≠ x₂ → ∃ a ∈ A, a x₁ ≠ a x₂)
--       (hB_sep : ∀ y₁ y₂ : Y, y₁ ≠ y₂ → ∃ b ∈ B, b y₁ ≠ b y₂) :
--       (ProductMaxPlusFamily A B : Set C(X × Y, ℝ)).SeparatesPointsStrongly := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalTensorProductUniversality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalTensorProductUniversality.lean#L267

-- Thm stub generated from Bridges/TropicalTensorProductUniversality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalTensorProductUniversality

/-!
# Tropical Tensor-Product Universality for Separable Bivariate EML Maps

This file formalizes a bivariate tropical Stone–Weierstrass / tensor-generation theorem:
given one-variable function families `A ⊆ C(X, ℝ)` and `B ⊆ C(Y, ℝ)` that separate
points, the product max-plus family on `X × Y` built from lifted functions of `A` and `B`
is uniformly dense in `C(X × Y, ℝ)`.

This is the idempotent/tropical analogue of algebraic tensor-product universality:
bivariate continuous functions are uniformly approximated by finite max-plus
combinations of separable terms.

## Main definitions

* `liftFst` / `liftSnd`: canonical embeddings of `C(X, ℝ)` and `C(Y, ℝ)` into `C(X × Y, ℝ)`
* `pureTensorMaxPlus`: the pure tensor `(x,y) ↦ a(x) + b(y)` in max-plus coordinates
* `ProductMaxPlusFamily`: the inductively generated max-plus family on `X × Y`

## Main results

* `productFamily_separates_points`: the product family separates all points of `X × Y`
* `productFamily_separatesPointsStrongly`: two-point interpolation for the product family
* `dense_productMaxPlusFamily`: density of the product max-plus family in `C(X × Y, ℝ)`
* `approx_productMaxPlusFamily`: ε-approximation version
* `dense_productMaxPlusFamily_univ`: universality for full function spaces

## Mathematical significance

This theorem upgrades one-variable tropical approximation to compositional multivariate
approximation: higher-dimensional EML maps can be built from one-dimensional factors by
tropical tensoring. It is the max-plus analogue of the classical fact that tensor products
of dense subalgebras are dense in the product-space function algebra.
-/

noncomputable section

open ContinuousMap Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ## Section 1: Lifting and Pure Tensors -/








/-! ## Section 2: Lift Homomorphism Properties -/









/-! ## Section 3: The Product Max-Plus Family -/


open ProductMaxPlusFamily

variable {A : Set C(X, ℝ)} {B : Set C(Y, ℝ)}











/-! ## Section 4: Product Point Separation -/




/-! ## Section 5: Strong Point Separation (Two-Point Interpolation)

We derive the strong two-point interpolation property required by the lattice
Stone–Weierstrass theorem. The proof constructs interpolating functions from
the max-plus closure structure (constants, addition, sup, negation, separation). -/

/-
Auxiliary: from a separating function, construct a nonneg function vanishing at `p₁`
and positive at `p₂`. Uses `f ↦ (f - const (f p₁)) ⊔ 0` to kill the value at `p₁`
while preserving positivity elsewhere.
-/

/-
Auxiliary: given a nonneg function vanishing at `p₁` and positive at `p₂`,
one can rescale to achieve any positive target value at `p₂` while keeping `p₁ = 0`.
-/

/-
**Two-point interpolation**: for any two distinct product points and any target values,
there exists a function in the product family attaining those values.
This is `Set.SeparatesPointsStrongly` for the product max-plus family.
-/

theorem productFamily_separatesPointsStrongly    {A : Set C(X, ℝ)} {B : Set C(Y, ℝ)}
    (hA_sep : ∀ x₁ x₂ : X, x₁ ≠ x₂ → ∃ a ∈ A, a x₁ ≠ a x₂)
    (hB_sep : ∀ y₁ y₂ : Y, y₁ ≠ y₂ → ∃ b ∈ B, b y₁ ≠ b y₂) :
    (ProductMaxPlusFamily A B : Set C(X × Y, ℝ)).SeparatesPointsStrongly := by sorry
