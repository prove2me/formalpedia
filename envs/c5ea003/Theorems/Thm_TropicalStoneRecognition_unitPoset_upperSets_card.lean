-- Prove2me | Theorems.Thm_TropicalStoneRecognition_unitPoset_upperSets_card
-- name    : TropicalStoneRecognition.unitPoset_upperSets_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:34:58.397346+00:00
-- url     : https://prove2.me/theorems/3b2998c8-31f5-493b-9731-08974bbed1a7
-- title:
--   UnitPoset upperSets card
-- statement:
--   Formal statement of `TropicalStoneRecognition.unitPoset_upperSets_card` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalStoneRecognition.unitPoset_upperSets_card:
--       Fintype.card (UpperSetFin unitPoset) = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalStoneRecognitionDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalStoneRecognitionDuality.lean#L397

-- Thm stub generated from Bridges/TropicalStoneRecognitionDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalStoneRecognitionDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Stone Recognition Duality via Idempotent Congruence Spectra

## Overview

This file establishes a finite duality between tropical recognition algebras
(finite commutative idempotent semirings) and finite spectral predicate spaces
(finite T₀ partial orders).

The central construction is the **upper-set idempotent semiring**: given a finite
poset X, the collection of upper sets forms a commutative semiring with union as
addition (idempotent) and intersection as multiplication (also idempotent). The
**principal upper set map** x ↦ ↑x = {y | x ≤ y} gives a contravariant
order-embedding — the finite analogue of Stone's representation theorem.

Combined with the congruence spectrum construction, this gives the duality:
  tropical language ↔ finite idempotent recognizer ↔ prime congruence spectral space

## Main Results

* `upperSetCommSemiring` — upper sets form a CommSemiring (union = +, ∩ = ×)
* `upperSet_idem_add`, `upperSet_idem_mul` — both operations are idempotent
* `principalUpper_injective` — Stone embedding is injective
* `principalUpper_order_embedding` — contravariant order characterization
* `upperSet_eq_union_principals` — basis decomposition
* `upperSet_absorption` — lattice absorption law
* `upperSet_union_inter_distrib` — union distributes over intersection
* `minimal_recognizer_card_eq` — uniqueness of minimal recognizers
* `finite_tropical_stone_representation` — main duality theorem
* `wordInterp_append` — word interpretation is multiplicative
-/


open Finset Function

noncomputable section

open TropicalStoneRecognition

/-! ## §1. Idempotent Semiring Infrastructure -/


attribute [instance] IdemSemiring.instCSR IdemSemiring.instFin IdemSemiring.instDec







/-! ## §2. Finite T₀ Partial Orders -/


attribute [instance] FinT0Poset.instFin FinT0Poset.instDec FinT0Poset.instPO
  FinT0Poset.instDecLE

/-! ## §3. Upper Sets as an Idempotent Semiring -/








instance (X : FinT0Poset) : Mul (UpperSetFin X) := ⟨UpperSetFin.inter⟩










/-! ## §4. Principal Upper Sets and the Stone Embedding -/










/-! ## §5. Congruences and the Spectrum -/







/-! ## §6. Tropical Language Recognition -/







/-! ## §7. Structural Properties -/







/-! ## §8. Concrete Examples -/


/-
The singleton poset has exactly 2 upper sets: ∅ and {()}.
-/

theorem TropicalStoneRecognition.unitPoset_upperSets_card:
    Fintype.card (UpperSetFin unitPoset) = 2 := by sorry
