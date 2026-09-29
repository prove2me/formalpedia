-- Prove2me | Theorems.Thm_TropicalContraction_MConvexExchangeFinsupp_supportContract
-- name    : TropicalContraction.MConvexExchangeFinsupp.supportContract
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:21:02.313732+00:00
-- url     : https://prove2.me/theorems/443ea210-c54b-4b81-a4d3-c5cbb03b42ee
-- title:
--   SupportContract
-- statement:
--   Formal statement of `TropicalContraction.MConvexExchangeFinsupp.supportContract` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalContraction.MConvexExchangeFinsupp.supportContract[Fintype σ]
--       {S : Finset (σ →₀ ℕ)} {i : σ}
--       (hS : MConvexExchangeFinsupp S) :
--       MConvexExchangeFinsupp (supportContract i S) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/TropicalContraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/TropicalContraction.lean#L201

-- Thm stub generated from Bridges/NeuralCoding/TropicalContraction.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_TropicalContraction
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

open TropicalContraction

variable {σ : Type*} [DecidableEq σ]

/-! ## Section 1: Core Definitions -/





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

theorem TropicalContraction.MConvexExchangeFinsupp.supportContract[Fintype σ]
    {S : Finset (σ →₀ ℕ)} {i : σ}
    (hS : MConvexExchangeFinsupp S) :
    MConvexExchangeFinsupp (supportContract i S) := by sorry
