-- Prove2me | solution 1 for TropicalStoneRecognition.unitPoset_upperSets_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:24:44.441232+00:00
-- url     : https://prove2.me/submissions/6f22f18e-657c-49ee-9b12-1e390848b3bc

-- Sol generated from Bridges/TropicalStoneRecognitionDuality.lean
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


/-
The chain on Fin 2 has 3 upper sets: ∅, {1}, {0, 1}.
-/

/-! ## §9. Word Interpretation Properties -/




/-! ## §10. Main Duality Theorem -/



open TropicalStoneRecognition in
theorem solution:
    Fintype.card (UpperSetFin unitPoset) = 2 := by
  convert Fintype.card_eq.2 _;
  convert rfl;
  convert Fintype.card_fin 2;
  refine' ⟨ _ ⟩;
  refine' Equiv.ofBijective ( fun x => if x.val = ∅ then 0 else 1 ) ⟨ _, _ ⟩;
  · intro x y hxy;
    rcases x with ⟨ x, hx ⟩ ; rcases y with ⟨ y, hy ⟩ ; simp_all +decide [ Finset.ext_iff ];
    split_ifs at hxy <;> simp_all +decide;
    aesop;
  · intro x;
    fin_cases x <;> [ exact ⟨ ⟨ ∅, by simp +decide ⟩, rfl ⟩ ; exact ⟨ ⟨ { () }, by simp +decide ⟩, rfl ⟩ ]
