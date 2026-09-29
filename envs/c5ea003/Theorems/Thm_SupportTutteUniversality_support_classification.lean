-- Prove2me | Theorems.Thm_SupportTutteUniversality_support_classification
-- name    : SupportTutteUniversality.support_classification
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:16:08.004646+00:00
-- url     : https://prove2.me/theorems/9b176fe5-9474-4ad2-aac7-49df48e1289a
-- title:
--   Support classification
-- statement:
--   Formal statement of `SupportTutteUniversality.support_classification` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SupportTutteUniversality.support_classification(S : Finset (ι →₀ ℕ)) :
--       S = ∅ ∨ S = {(0 : ι →₀ ℕ)} ∨
--       (∃ i, IsOrdCoord S i) ∨ (∃ i, IsSLoop S i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/old/SupportTutteUniversality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/old/SupportTutteUniversality.lean#L158

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

theorem SupportTutteUniversality.support_classification(S : Finset (ι →₀ ℕ)) :
    S = ∅ ∨ S = {(0 : ι →₀ ℕ)} ∨
    (∃ i, IsOrdCoord S i) ∨ (∃ i, IsSLoop S i) := by sorry
