-- Prove2me | solution 1 for TropicalTrapdoor.exists_certified_pair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:10:05.117892+00:00
-- url     : https://prove2.me/submissions/e5fd8f30-2a8c-42c6-be38-d0cb75e2c2bc

-- Sol generated from Bridges/TropicalResiduationTrapdoorDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalResiduationTrapdoorDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Residuation Trapdoor Duality

## Overview

This module formalizes a structural theory of trapdoors in tropical (min-plus) matrix
algebra. The central construction is the **public map** F_{A,B}(X) = A ⊗ X ⊗ B,
where ⊗ denotes min-plus matrix multiplication.

## Main Results

### Algebraic Foundations
* `tropMul_assoc` — min-plus matrix multiplication is associative
* `tropMul_entry_le` — each entry of a product is bounded by any witness term
* `boundedEntries_tropMul` — bounded entries are preserved under multiplication

### Ordering & Monotonicity
* `tropLe_refl`, `tropLe_trans`, `tropLe_antisymm` — entry-wise ordering is a partial order
* `tropMul_mono_left`, `tropMul_mono_right` — tropical multiplication is order-monotone
* `publicMap_mono` — the public map preserves tropical ordering

### Residuation Class Structure
* `resLe_trans` — witness-based residuation is transitive
* `sameResiduationClass_symm`, `sameResiduationClass_trans` — class equivalence properties

### Compression & Spectrum Invariance
* `rowMins_tropMul` — row minima transform covariantly under left multiplication
* `colMins_tropMul` — column minima transform covariantly under right multiplication
* `rowMins_additiveShift` — row minima shift by additive constants
* `residuationSpectrum_additiveShift` — spectrum is invariant under additive shifts

### Fiber Ambiguity (the breakthrough results)
* `publicMap_zero_fiber_collapse` — zero-matrix public map collapses to global minimum
* `inverse_fiber_contains_incomparable_pair` — fibers contain tropically incomparable pairs
* `inverse_fiber_nontrivial` — for n ≥ 2, there exist non-trivial fibers

## Cross-Domain Connections

- **Post-quantum cryptography**: hardness from idempotent algebraic ambiguity
- **Tropical geometry**: residuation classes as tropical orbit strata
- **Ordered algebra**: inversion hardness as preorder/antichain structure
- **Information theory**: compression profiles as public summaries with tropical information loss
-/

open Finset BigOperators

open TropicalTrapdoor


/-! ## Section 1: Core Definitions -/


















/-! ## Section 2: Basic Algebraic Properties -/



/-
**Associativity of min-plus matrix multiplication.**
    This is the fundamental algebraic property enabling compositional reasoning
    about tropical matrix semigroups.
-/

/-
**Bounded entries are preserved under tropical multiplication.**
    If A is K_A-bounded and B is K_B-bounded, then A ⊗ B is (K_A + K_B)-bounded.
-/

/-
**Bounded entries are preserved under the public map.**
-/

/-! ## Section 3: Entry-wise Ordering -/




/-
**Left tropical multiplication is monotone in the right factor.**
-/

/-
**Right tropical multiplication is monotone in the left factor.**
-/


/-! ## Section 4: Residuation Class Structure -/

/-
**Transitivity of witness-based residuation.**
    If X = L₁ ⊗ Y ⊗ R₁ and Y = L₂ ⊗ Z ⊗ R₂, then
    X = (L₁⊗L₂) ⊗ Z ⊗ (R₂⊗R₁).
-/



/-! ## Section 5: Compression & Spectrum Functoriality -/

/-
**Row minima transform covariantly under left multiplication.**
    `rowMins(A ⊗ X) i = min_k (A i k + rowMins X k)`

    This shows that compression data has a clean transformation law
    under tropical matrix action: left multiplication by A acts on
    row minima via tropical matrix-vector multiplication.
-/

/-
**Column minima transform covariantly under right multiplication.**
    `colMins(X ⊗ B) j = min_k (colMins X k + B k j)`
-/

/-
**Row minima shift linearly under additive shift.**
-/

/-
**The residuation spectrum is invariant under additive shifts.**
    This is a key structural result: the spectrum captures the "shape"
    of a matrix independent of its absolute level, making it a natural
    quotient invariant for tropical cryptography.
-/

/-! ## Section 6: Constant Matrix Interactions -/


/-
**Tropical multiplication by a constant matrix on the left extracts column minima.**
    `(constMat c ⊗ X)ᵢⱼ = c + colMins X j`
-/

/-
**Tropical multiplication by a constant matrix on the right extracts row minima.**
    `(X ⊗ constMat c)ᵢⱼ = rowMins X i + c`
-/

/-
**The public map with zero constant matrices collapses to the global minimum.**
    This is the core structural lemma for fiber ambiguity.
-/

/-! ## Section 7: Fiber Ambiguity — The Breakthrough Results -/






/-
The two witness matrices have the same global minimum (both = 0).
-/

/-
The two witness matrices are **tropically incomparable**:
    neither X₁ ≤ X₂ nor X₂ ≤ X₁ in entry-wise ordering.
    This is the structural content of non-uniqueness.
-/

/-
**Inverse fibers of the public map contain incomparable pairs.**
    For A = B = 0 (the constant-zero matrix), the fiber over the common image
    contains two 1-bounded matrices that are:
    1. Distinct
    2. Map to the same image under the public map
    3. Incomparable in the tropical ordering

    This establishes that non-uniqueness of inversion is a **structural property**,
    not merely a computational barrier. The incomparability means no single
    tropical ordering can resolve the ambiguity.
-/

/-
**General fiber ambiguity theorem.**
    For any dimension n ≥ 2, there exist public matrices and 1-bounded preimages
    that map to the same image but are distinct. This shows that fiber ambiguity
    is a dimensional phenomenon, not an artifact of small examples.
-/

/-! ## Section 8: Signature Invariance Under Public Action -/


/-
**The public map preserves compression profiles functorially.**
    The compression profile of the image depends on the profile of the
    preimage through a computable transformation.
-/

/-! ## Section 9: Certified Key Generation Infrastructure -/

/-
**Existence of certified public-secret pairs.**
    For any dimension n ≥ 2 and any bound K ≥ 1, there exist:
    - Public matrices A, B (the public key)
    - A secret matrix X
    - All bounded by K
    such that the public map exhibits non-trivial fiber collapse.
-/


open TropicalTrapdoor in
theorem solution{n : ℕ} (hn : 2 ≤ n) :
    ∃ (A B X Y : TropMat n),
      boundedEntries 1 A ∧ boundedEntries 1 B ∧
      boundedEntries 1 X ∧ boundedEntries 1 Y ∧
      X ≠ Y ∧
      publicMap A B X = publicMap A B Y ∧
      FiberCollapseWitness A B (publicMap A B X) 1 := by
  refine' ⟨ 0, 0, _ ⟩;
  refine' ⟨ _, _, _, _, _, _, _, _ ⟩ <;> norm_num [ boundedEntries, publicMap, FiberCollapseWitness ];
  exact fun i j => if i = ⟨ 0, by linarith ⟩ ∧ j = ⟨ 0, by linarith ⟩ then 0 else 1;
  exact fun i j => if i = ⟨ 0, by linarith ⟩ ∧ j = ⟨ 1, by linarith ⟩ then 0 else 1;
  · intro i j; split_ifs <;> norm_num;
  · intro i j; split_ifs <;> norm_num;
  · exact fun h => by have := congr_fun ( congr_fun h ⟨ 0, by linarith ⟩ ) ⟨ 0, by linarith ⟩ ; simp +decide at this;
  · refine' ⟨ _, _ ⟩;
    · ext i j; simp +decide [ tropMul ] ;
      refine' le_antisymm _ _ <;> simp +decide [ Finset.inf'_le ];
      · exact fun i j => ⟨ ⟨ 0, by linarith ⟩, ⟨ 0, by linarith ⟩, by aesop ⟩;
      · intro b b_1; use ⟨ 1, by linarith ⟩, ⟨ 0, by linarith ⟩ ; aesop;
    · refine' ⟨ fun i j => if i = ⟨ 0, by linarith ⟩ ∧ j = ⟨ 0, by linarith ⟩ then 0 else 1, _, fun i j => if i = ⟨ 0, by linarith ⟩ ∧ j = ⟨ 1, by linarith ⟩ then 0 else 1, _, _, _, _ ⟩ <;> norm_num [ tropMul ];
      · intro i j; split_ifs <;> norm_num;
      · intro i j; split_ifs <;> norm_num;
      · exact fun h => by have := congr_fun ( congr_fun h ⟨ 0, by linarith ⟩ ) ⟨ 0, by linarith ⟩ ; simp +decide at this;
      · ext i j; simp +decide [ tropMul ] ;
        refine' le_antisymm _ _ <;> simp +decide [ Finset.inf'_le, Finset.le_inf' ];
        · intro b b_1; use ⟨ 1, by linarith ⟩, ⟨ 0, by linarith ⟩ ; aesop;
        · intro b b_1; use ⟨ 0, by linarith ⟩, ⟨ 0, by linarith ⟩ ; aesop;
