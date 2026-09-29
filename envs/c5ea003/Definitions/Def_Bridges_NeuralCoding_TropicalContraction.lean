-- Prove2me | Definitions.Def_Bridges_NeuralCoding_TropicalContraction
-- name    : Bridges_NeuralCoding_TropicalContraction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:34.109789+00:00
-- url     : https://prove2.me/theorems/2390e095-a18c-456d-adc9-ef104fe9d46b
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_TropicalContraction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.TropicalContraction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/TropicalContraction.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical Contraction and Support Truncation

This file establishes the formal bridge between **support contraction** of multivariate
polynomials, **tropicalization** of coefficients/exponents, and **truncation of Newton
support/polytopes**. The central result is that contraction — removing one unit of mass
in a chosen coordinate direction — commutes with the passage to tropical (exponent-level)
data, and preserves the M-convex exchange structure.

## Main Definitions

* `TropicalSupport` — A tropical polynomial represented by its finite support and weight
* `exponentContract` — Contract an exponent vector by removing one unit in coordinate `i`
* `supportContract` — Contract a finite set of exponent vectors in direction `i`
* `tropicalTruncate` — Truncate a tropical support in direction `i`
* `MConvexExchangeFinsupp` — M-convex exchange property on `Finset (σ →₀ ℕ)`

## Main Results

1. `supp_tropicalTruncate_eq_contract` — Tropical truncation support equals support contraction
2. `supportContract_mem_iff` — Membership characterization of support contraction
3. `image_supportContract_add_single_eq_filter` — Inverse image characterization
4. `MConvexExchangeFinsupp.supportContract` — Exchange preserved under contraction

## References

* Murota, "Discrete Convex Analysis", SIAM, 2003
* Maclagan–Sturmfels, "Introduction to Tropical Geometry", AMS, 2015
-/

open Finset Finsupp BigOperators

noncomputable section

namespace TropicalContraction

variable {σ : Type*} [DecidableEq σ]

/-! ## Section 1: Core Definitions -/

/-- A tropical support is a finite set of exponent vectors with integer weights.
    This captures the tropical shadow of a multivariate polynomial: we retain
    only the support (which monomials appear) and a weight function (the tropical
    valuation of each coefficient). -/
structure TropicalSupport (σ : Type*) [DecidableEq σ] where
  /-- The finite support: exponent vectors of monomials that appear. -/
  supp : Finset (σ →₀ ℕ)
  /-- Weight function: the tropical valuation of each monomial's coefficient. -/
  weight : (σ →₀ ℕ) → ℤ
  /-- Weights are zero outside the support. -/
  weight_mem : ∀ m, m ∉ supp → weight m = 0

/-- Contract an exponent vector in direction `i`: subtract one from coordinate `i`
    if it is positive, returning `none` if the coordinate is already zero.

    Mathematically: given `m ∈ ℕ^σ` and `i ∈ σ`,
    - if `m(i) > 0`, return `m - e_i`
    - if `m(i) = 0`, return `none` -/
def exponentContract (i : σ) (m : σ →₀ ℕ) : Option (σ →₀ ℕ) :=
  if m i = 0 then none
  else some (m.update i (m i - 1))

/-- Support contraction in direction `i`: filter to exponents with positive `i`-coordinate,
    then subtract `e_i` from each. -/
def supportContract (i : σ) (S : Finset (σ →₀ ℕ)) : Finset (σ →₀ ℕ) :=
  (S.filter (fun m => 0 < m i)).image (fun m => m.update i (m i - 1))

/-- Truncate a tropical support in direction `i`: contract the support and
    propagate weights from the original exponent vectors. -/
def tropicalTruncate (i : σ) (T : TropicalSupport σ) : TropicalSupport σ where
  supp := supportContract i T.supp
  weight := fun m' =>
    if m' ∈ supportContract i T.supp then
      T.weight (m'.update i (m' i + 1))
    else 0
  weight_mem := fun m hm => by simp [hm]

/-! ## Section 2: Characterization Lemmas -/






/-! ## Section 3: Tropical Truncation = Support Contraction -/


/-! ## Section 4: Inverse Image Characterization -/

/-
The contraction map `m ↦ m.update i (m i - 1)` is injective on vectors with
    positive `i`-coordinate.
-/

/-
Adding `e_i` back to a contracted support recovers the filtered original support.
    This is the key invertibility property: contraction is a bijection between
    `{m ∈ S | m(i) > 0}` and `supportContract i S`.
-/

/-! ## Section 5: M-Convex Exchange Property -/

/-- The M-convex symmetric exchange property for finite support sets in `σ →₀ ℕ`.
    For any `α, β ∈ S` with `α(i) > β(i)`, there exists `j` with `α(j) < β(j)`
    such that `α - e_i + e_j ∈ S`.

    This is the foundational axiom of discrete convex analysis (Murota 2003). -/
def MConvexExchangeFinsupp [Fintype σ] (S : Finset (σ →₀ ℕ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ k : σ,
    β k < α k →
    ∃ j : σ, α j < β j ∧
      (α.update k (α k - 1)).update j (α j + 1) ∈ S

/-- Alias: tropical exchange is defined as the same exchange property on supports. -/
def TropicalExchange [Fintype σ] (S : Finset (σ →₀ ℕ)) : Prop :=
  MConvexExchangeFinsupp S


/-! ## Section 6: Contraction Preserves Exchange -/

/-
**Theorem 2**: The M-convex exchange property is preserved under support contraction.

    If `S` satisfies the symmetric exchange axiom, then `supportContract i S` also satisfies
    the symmetric exchange axiom. This is the tropical stability theorem: the discrete convex
    structure is invariant under coordinate contraction/truncation.

    **Proof strategy**: Given `α', β' ∈ supportContract i S` with `α'(k) > β'(k)`,
    lift to `α, β ∈ S` with `α(i) > 0, β(i) > 0`, apply exchange in `S`,
    and project the witness back down through contraction.
-/


/-! ## Section 7: Weighted Tropical M-Convexity -/


/-! ## Section 8: Support Contraction Properties -/

/-
Support contraction preserves cardinality of the positive-coordinate subset.
-/

/-
Support contraction is monotone: if `S ⊆ T` then
    `supportContract i S ⊆ supportContract i T`.
-/


/-
A singleton contracts to a singleton or empty set.
-/

end TropicalContraction


