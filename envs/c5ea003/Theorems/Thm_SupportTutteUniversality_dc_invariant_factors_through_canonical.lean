-- Prove2me | Theorems.Thm_SupportTutteUniversality_dc_invariant_factors_through_canonical
-- name    : SupportTutteUniversality.dc_invariant_factors_through_canonical
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:16:10.020732+00:00
-- url     : https://prove2.me/theorems/56d2d9db-e814-4f1b-bb87-2b58cf90fb5e
-- title:
--   Theorem C (Universal Factorization).
-- statement:
--   **Theorem C (Universal Factorization).**
--   Any function satisfying the DC recurrence with loop weight `xL` equals
--   `canonicalSupportEval xL`. Proved by strong induction on `sMeasure`,
--   using `rcases` on the support classification at each step.
--
--   ```lean
--   theorem SupportTutteUniversality.dc_invariant_factors_through_canonical    {R : Type*} [CommSemiring R] (xL : R)
--       (f : Finset (ι →₀ ℕ) → R)
--       (hf_empty : f ∅ = 1)
--       (hf_zero : f {(0 : ι →₀ ℕ)} = 1)
--       (hf_ord : ∀ S i, IsOrdCoord S i →
--         f S = f (sDelete S i) + f (sContract S i))
--       (hf_loop : ∀ S i, IsSLoop S i → S.Nonempty →
--         f S = xL * f (sContract S i))
--       (S : Finset (ι →₀ ℕ)) :
--       f S = canonicalSupportEval xL S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/old/SupportTutteUniversality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/old/SupportTutteUniversality.lean#L208

-- Thm stub generated from Bridges/old/SupportTutteUniversality.lean
import Mathlib
import Definitions.Def_Bridges_old_SupportTutteUniversality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Universal Support-Tutte Invariant: Full Universality and Cross-Domain Bridge

This file establishes the **universal factorization theorem** for
deletion–contraction invariants on M-convex supports, proves a cardinality
specialization, and provides a cross-domain bridge to matroid theory via
binary supports.

## Main Results

* `dc_invariant_factors_through_canonical` — Universal factorization (Theorem C)
* `dc_invariant_unique` — Uniqueness corollary (uses multi-step calc)
* `canonicalSupportEval_one_eq_card` — Cardinality specialization (Theorem B)
* `activity_partition` — Activity counting theorem
* `binary_support_card_recursion` — Bridge to matroid theory (Theorem D)

## References

* Murota, "Discrete Convex Analysis", SIAM, 2003
* Brylawski–Oxley, "The Tutte polynomial and its applications", 1992
-/

open Finset BigOperators Finsupp

attribute [local instance] Classical.propDecidable

open SupportTutteUniversality

variable {ι : Type*} [DecidableEq ι]

/-! ## Section 1: Core Definitions -/








/-! ## Section 2: Basic Lemmas -/








/-! ## Section 3: Measure Descent -/




/-! ## Section 4: Support Classification -/


/-! ## Section 5: Canonical Evaluation -/


/-! ## Section 6: Theorem A — Base Cases -/



/-! ## Section 7: Theorem C — Universal Factorization -/

theorem SupportTutteUniversality.dc_invariant_factors_through_canonical    {R : Type*} [CommSemiring R] (xL : R)
    (f : Finset (ι →₀ ℕ) → R)
    (hf_empty : f ∅ = 1)
    (hf_zero : f {(0 : ι →₀ ℕ)} = 1)
    (hf_ord : ∀ S i, IsOrdCoord S i →
      f S = f (sDelete S i) + f (sContract S i))
    (hf_loop : ∀ S i, IsSLoop S i → S.Nonempty →
      f S = xL * f (sContract S i))
    (S : Finset (ι →₀ ℕ)) :
    f S = canonicalSupportEval xL S := by sorry
