-- Prove2me | Theorems.Thm_SupportTutteUniversality_canonicalSupportEval_one_eq_card
-- name    : SupportTutteUniversality.canonicalSupportEval_one_eq_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:16:17.530805+00:00
-- url     : https://prove2.me/theorems/4c735582-28f9-44b2-b874-d36c0b735eed
-- title:
--   CanonicalSupportEval one eq card
-- statement:
--   Formal statement of `SupportTutteUniversality.canonicalSupportEval_one_eq_card` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SupportTutteUniversality.canonicalSupportEval_one_eq_card    (S : Finset (ι →₀ ℕ)) (hne : S.Nonempty) :
--       canonicalSupportEval (1 : ℕ) S = S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/old/SupportTutteUniversality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/old/SupportTutteUniversality.lean#L289

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


/-! ## Section 8: Uniqueness Corollary -/


/-! ## Section 9: Partition and Cardinality -/




/-! ## Section 10: Theorem B — Cardinality Specialization -/

/-
**Theorem B (Cardinality specialization).**
    Evaluating at `xL = 1` recovers the support cardinality.
-/

theorem SupportTutteUniversality.canonicalSupportEval_one_eq_card    (S : Finset (ι →₀ ℕ)) (hne : S.Nonempty) :
    canonicalSupportEval (1 : ℕ) S = S.card := by sorry
