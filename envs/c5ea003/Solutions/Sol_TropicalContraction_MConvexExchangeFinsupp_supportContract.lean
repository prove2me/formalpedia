-- Prove2me | solution 1 for TropicalContraction.MConvexExchangeFinsupp.supportContract
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:05:00.153654+00:00
-- url     : https://prove2.me/submissions/11b9425e-0123-4ac6-b110-51de255ec0ad

-- Sol generated from Bridges/NeuralCoding/TropicalContraction.lean
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





/-- Membership in the contracted support. -/
theorem supportContract_mem_iff {i : σ} {S : Finset (σ →₀ ℕ)} {m' : σ →₀ ℕ} :
    m' ∈ supportContract i S ↔
      ∃ m ∈ S, 0 < m i ∧ m' = m.update i (m i - 1) := by
  simp [supportContract, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨m, ⟨hm, hpos⟩, rfl⟩
    exact ⟨m, hm, hpos, rfl⟩
  · rintro ⟨m, hm, hpos, rfl⟩
    exact ⟨m, ⟨hm, hpos⟩, rfl⟩

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


open TropicalContraction in
theorem solution[Fintype σ]
    {S : Finset (σ →₀ ℕ)} {i : σ}
    (hS : MConvexExchangeFinsupp S) :
    MConvexExchangeFinsupp (supportContract i S) := by
  intro α' hα' β' hβ' k hk;
  -- Unpack α' and β'. By supportContract_mem_iff, there exist α, β ∈ S with 0 < α i, 0 < β i, α' = α.update i (α i - 1), β' = β.update i (β i - 1).
  obtain ⟨α, hαS, hαi, rfl⟩ := supportContract_mem_iff.mp hα'
  obtain ⟨β, hβS, hβi, rfl⟩ := supportContract_mem_iff.mp hβ';
  -- By hS, there exists j with α j < β j and e := (α.update k (α k - 1)).update j (α j + 1) ∈ S.
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j, α j < β j ∧ (α.update k (α k - 1)).update j (α j + 1) ∈ S := by
    apply hS α hαS β hβS k;
    grind;
  refine' ⟨ j, _, _ ⟩;
  · grind;
  · refine' Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ hj₂, _ ⟩, _ ⟩;
    · grind;
    · grind
