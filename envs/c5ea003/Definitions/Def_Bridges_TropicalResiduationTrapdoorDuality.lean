-- Prove2me | Definitions.Def_Bridges_TropicalResiduationTrapdoorDuality
-- name    : Bridges_TropicalResiduationTrapdoorDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:00.432422+00:00
-- url     : https://prove2.me/theorems/b9dbbd8f-6740-411c-bcdd-6b691db924c2
-- title:
--   Aether Catalog definitions — Bridges_TropicalResiduationTrapdoorDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalResiduationTrapdoorDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalResiduationTrapdoorDuality.lean by skeleton subtraction
import Mathlib
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

namespace TropicalTrapdoor

/-- Tropical matrix: n×n matrix with integer entries, under min-plus operations. -/
abbrev TropMat (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

/-! ## Section 1: Core Definitions -/

/-- **Min-plus matrix multiplication**: `(A ⊗ B)ᵢⱼ = min_k (Aᵢₖ + Bₖⱼ)`.
    This is the fundamental operation of tropical linear algebra. -/
def tropMul {n : ℕ} (A B : TropMat n) : TropMat n :=
  fun i j => Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (fun k => A i k + B k j)

/-- **The public map** `F_{A,B}(X) = A ⊗ X ⊗ B`.
    Public keys A, B define a tropical conjugation action on secret matrix X. -/
def publicMap {n : ℕ} (A B X : TropMat n) : TropMat n :=
  tropMul (tropMul A X) B

/-- A matrix has **bounded entries** if all entries have absolute value ≤ K. -/
def boundedEntries {n : ℕ} (K : ℕ) (X : TropMat n) : Prop :=
  ∀ i j, |X i j| ≤ (K : ℤ)

/-- **Row minima** of a tropical matrix. -/
def rowMins {n : ℕ} [NeZero n] (X : TropMat n) (i : Fin n) : ℤ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => X i j)

/-- **Column minima** of a tropical matrix. -/
def colMins {n : ℕ} [NeZero n] (X : TropMat n) (j : Fin n) : ℤ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => X i j)

/-- **Additive shift**: translate all entries by a constant. -/
def additiveShift {n : ℕ} (c : ℤ) (X : TropMat n) : TropMat n :=
  fun i j => X i j + c

/-- **Compression profile**: row and column minima vectors.
    These are the publicly extractable invariants of a tropical matrix. -/
structure CompressionProfile (n : ℕ) where
  rowPart : Fin n → ℤ
  colPart : Fin n → ℤ
  deriving DecidableEq

/-- Extract the compression profile of a tropical matrix. -/
noncomputable def compressionProfile {n : ℕ} [NeZero n] (X : TropMat n) :
    CompressionProfile n where
  rowPart := rowMins X
  colPart := colMins X

/-- **Entry-wise tropical ordering**: X ≤_trop Y iff Xᵢⱼ ≤ Yᵢⱼ for all i,j. -/
def tropLe {n : ℕ} (X Y : TropMat n) : Prop :=
  ∀ i j, X i j ≤ Y i j

/-- **Witness-based residuation**: X ≤_res Y iff X = L ⊗ Y ⊗ R for some L, R.
    Captures "derivable from" under tropical side-actions. -/
def resLe {n : ℕ} (X Y : TropMat n) : Prop :=
  ∃ L R : TropMat n, X = tropMul (tropMul L Y) R

/-- **Same residuation class**: mutual residuation derivability. -/
def sameResiduationClass {n : ℕ} (X Y : TropMat n) : Prop :=
  resLe X Y ∧ resLe Y X

/-- **Residuation spectrum**: sorted gaps from row minima.
    Records the sorted list of `Xᵢⱼ - rowMin_i` for all i,j. -/
structure ResiduationSpectrum (n : ℕ) where
  gaps : List ℤ
  deriving DecidableEq

/-- Extract the residuation spectrum from a tropical matrix. -/
noncomputable def residuationSpectrum {n : ℕ} [NeZero n] (X : TropMat n) :
    ResiduationSpectrum n where
  gaps := (((List.finRange n).flatMap (fun i =>
    (List.finRange n).map (fun j => X i j - rowMins X i))).mergeSort (· ≤ ·))

/-- **Public signature** combining compression profile and residuation spectrum. -/
structure Signature (n : ℕ) where
  profile : CompressionProfile n
  spectrum : ResiduationSpectrum n
  deriving DecidableEq

/-- Extract the full signature of a tropical matrix. -/
noncomputable def signature {n : ℕ} [NeZero n] (X : TropMat n) : Signature n where
  profile := compressionProfile X
  spectrum := residuationSpectrum X


/-- **Fiber collapse witness**: the public map collapses distinct bounded matrices. -/
def FiberCollapseWitness {n : ℕ} (A B Z : TropMat n) (K : ℕ) : Prop :=
  ∃ X Y : TropMat n, boundedEntries K X ∧ boundedEntries K Y ∧
    X ≠ Y ∧ publicMap A B X = Z ∧ publicMap A B Y = Z

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

/-- The constant matrix: all entries equal to c. -/
def constMat {n : ℕ} (c : ℤ) : TropMat n := fun _ _ => c

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

/-- First witness matrix for fiber ambiguity: entry (0,0) = 0, all others = 1. -/
def fiberWitness1 : TropMat 2 :=
  fun i j => if i = 0 ∧ j = 0 then 0 else 1

/-- Second witness matrix for fiber ambiguity: entry (0,1) = 0, all others = 1. -/
def fiberWitness2 : TropMat 2 :=
  fun i j => if i = 0 ∧ j = 1 then 0 else 1




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

end TropicalTrapdoor


