-- Prove2me | Definitions.Def_Bridges_ECOCDefs
-- name    : Bridges_ECOCDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:49.889137+00:00
-- url     : https://prove2.me/theorems/8d332856-9797-4be5-aca0-641abb0a9bf9
-- title:
--   Aether Catalog definitions — Bridges_ECOCDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ECOCDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ECOCDefs.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ECOC Robustness for Tropical Satake Score Classifiers — Definitions

This file establishes the core definitions for Error-Correcting Output Code (ECOC)
classifiers built from tropical Satake score gaps. The key objects are:

- `CodeMatrix`: a ±1 code matrix assigning binary codewords to classes
- `SignedBitScore`, `softScore`: the signed bit-gap and aggregate soft-decoding scores
- `disagreeBits`: the Hamming support of the codeword difference between two classes
- `BitGapLipschitzOn`: the per-bit Lipschitz condition abstracting tropical Hecke estimates
- `pairAdvantage`, `certifiedRadius`: the weighted code-distance and explicit robustness radius

These definitions form the foundation for the robustness theorems proved in
`Bridges.ECOCRobustSoft` and `Bridges.ECOCRobustHard`.
-/

open scoped BigOperators
open Finset

/-! ## Core Definitions -/

/-- A code matrix assigns an integer code value to each (class, bit) pair. -/
def CodeMatrix (n m : ℕ) := Fin n → Fin m → ℤ

/-- A valid code matrix has all entries in {+1, -1}. -/
def ValidCodeMatrix {n m : ℕ} (C : CodeMatrix n m) : Prop :=
  ∀ y j, C y j = 1 ∨ C y j = -1

/-- The signed bit score for class `y` on bit `j` at input `x`. -/
def SignedBitScore {n m : ℕ} {α : Type*}
    (C : CodeMatrix n m) (g : Fin m → α → ℝ)
    (y : Fin n) (j : Fin m) (x : α) : ℝ :=
  (C y j : ℝ) * g j x

/-- The set of bit positions where classes `y` and `z` have different codewords. -/
def disagreeBits {n m : ℕ} (C : CodeMatrix n m) (y z : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => C y j ≠ C z j)








/-- A code matrix is injective if distinct classes have distinct codewords. -/
def CodeInjective {n m : ℕ} (C : CodeMatrix n m) : Prop :=
  Function.Injective C

/-! ## Key algebraic lemmas about ±1 codes -/


