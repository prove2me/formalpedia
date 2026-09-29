-- Prove2me | Definitions.Def_Bridges_TropicalIsogenyRigidity
-- name    : Bridges_TropicalIsogenyRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:30.140287+00:00
-- url     : https://prove2.me/theorems/475fbcb2-f7e1-4e1a-b43a-388282ea68de
-- title:
--   Aether Catalog definitions — Bridges_TropicalIsogenyRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalIsogenyRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalIsogenyRigidity.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Isogeny Rigidity via Idempotent Jacobian Semimodules
  and Certified Trapdoor Reconstruction

## Overview

We establish a tropical isogeny rigidity theorem: for a finite metric graph
(tropical curve) `Γ` equipped with a harmonic correspondence `Φ`, the induced
min-plus linear map on the discrete Jacobian `J(Γ) ≅ ℤ^g` is uniquely determined
by evaluation on `g` coordinate valuation characters. Moreover, equal induced
actions force the underlying tropical matrices to be identical, yielding
**principal equivalence** of the correspondences.

This opens a bridge between **tropical geometry**, **idempotent linear algebra**,
**harmonic graph theory**, and **post-quantum cryptography**: the "trapdoor" is a
hidden harmonic correspondence reconstructed from min-plus spectral fingerprints.

## Main Results

### Algebraic Foundations
* `trop_distrib` — tropical distributivity: `a + min(b,c) = min(a+b, a+c)`
* `trop_absorption` — idempotent absorption in min-plus

### Tropical Matrix Rigidity
* `tropMV_testVec_eq` — test vectors recover tropical matrix entries
* `tropMat_determined_by_action` — **Key Lemma**: a tropical matrix is
  uniquely determined by its min-plus action on all vectors

### Separation Framework
* `separating_forces_eq` — separating characters force function equality
* `coord_separates` — coordinate projections separate `ℤ^g`

### Main Theorem Chain
* `finite_extremal_jacobian_reconstruction` — **Theorem A**: spectral data
  determines the induced Jacobian action
* `harmonic_correspondence_rigidity` — **Theorem B**: equal Jacobian actions
  force principal equivalence of correspondences
* `compressed_spectral_data_recovers_correspondence` — **Master Theorem**:
  compressed spectral data recovers the correspondence class
* `spectral_collision_iff_congruence` — **Theorem C**: collision
  characterization via congruence kernel
* `certified_separation` — **Theorem D**: certified collision separation
-/

noncomputable section

open Function Finset

set_option maxHeartbeats 400000

namespace TropicalIsogenyRigidity

/-! ## §1 Min-Plus Algebraic Foundations

The min-plus semiring `(ℤ, min, +)` underlies all tropical geometry.
We establish its key algebraic properties as certified lemmas. -/





/-! ## §2 Tropical Matrix-Vector Products

Min-plus matrix-vector multiplication `(Av)_i = min_j(A_{ij} + v_j)` models
the action of a tropical correspondence on the Jacobian semimodule. -/

section TropicalMatrix

variable {g : ℕ} (hg : 0 < g)

/-- **Min-plus matrix-vector product**: `(Av)_i = min_j (A_{ij} + v_j)`. -/
def tropMV (A : Fin g → Fin g → ℤ) (v : Fin g → ℤ) : Fin g → ℤ :=
  fun i => univ.inf' (univ_nonempty_iff.mpr ⟨⟨0, hg⟩⟩) (fun j => A i j + v j)



/-- **Test vector** concentrating mass at index `j`:
    `v_j = 0`, `v_k = M` for `k ≠ j`. -/
def testVec (j : Fin g) (M : ℤ) : Fin g → ℤ :=
  fun k => if k = j then 0 else M



/-
**Matrix entry recovery**: The min-plus product with a test vector recovers
    the matrix entry `A i j`, provided `M` is large enough.
-/

/-
For any matrix entries and row index, there exists a sufficiently large `M`
    such that the test vector at column `j` recovers entry `A i j`.
-/

/-
**Tropical matrix rigidity**: Two tropical matrices with identical
    min-plus actions on all vectors must be equal.

    This is the core technical lemma. The proof constructs, for each entry `(i,j)`,
    a test vector that isolates that entry via the min-plus product.
-/

end TropicalMatrix

/-! ## §3 Abstract Separation Framework

A family of evaluation functions ("characters") on a type `J` is *separating*
if agreement on all characters implies equality of elements. This abstracts the
role of extremal valuation characters on divisor-class semimodules. -/

/-- A family of functions is *separating* if agreement on all functions
    implies equality of arguments. -/
def IsSeparating {ι J R : Type*} (chars : ι → J → R) : Prop :=
  ∀ x y : J, (∀ i, chars i x = chars i y) → x = y






/-! ## §4 Tropical Curve and Jacobian Structures -/

/-- **Tropical curve data**: abstract interface for a finite metric graph,
    parameterized by its genus (first Betti number). -/
structure TropicalCurveData where
  /-- Genus (first Betti number) of the metric graph -/
  genus : ℕ
  /-- Positive genus ensures a nontrivial Jacobian -/
  genus_pos : 0 < genus

variable {Γ : TropicalCurveData}

/-- The **discrete tropical Jacobian** `J(Γ) ≅ ℤ^g`, the idempotent
    divisor-class semimodule of a tropical curve of genus `g`. -/
abbrev Jacobian (Γ : TropicalCurveData) := Fin Γ.genus → ℤ

/-! ## §5 Harmonic Correspondences and Induced Maps -/

/-- A **harmonic correspondence** on `Γ`, encoded as a tropical matrix
    (the min-plus linear map it induces on the Jacobian) together with
    a combinatorial degree. -/
structure HarmonicCorr (Γ : TropicalCurveData) where
  /-- Tropical matrix encoding the correspondence -/
  matrix : Fin Γ.genus → Fin Γ.genus → ℤ
  /-- Degree of the correspondence -/
  degree : ℕ

/-- The **induced map** of a harmonic correspondence on the Jacobian,
    via min-plus matrix-vector product. -/
def HarmonicCorr.induced (Φ : HarmonicCorr Γ) : Jacobian Γ → Jacobian Γ :=
  tropMV Γ.genus_pos Φ.matrix

/-- **Principal equivalence**: two correspondences are principally equivalent
    when their tropical matrices agree (they induce identical Jacobian actions).
    Correspondences may still differ in degree or other combinatorial data. -/
def PrincipalEquiv (Φ Ψ : HarmonicCorr Γ) : Prop :=
  Φ.matrix = Ψ.matrix





/-! ## §6 Compressed Spectral Data and Congruence Kernel -/

/-- Two correspondences have the **same compressed spectral data** when
    their induced maps agree on all coordinate valuation characters. -/
def SameSpectralData (Φ Ψ : HarmonicCorr Γ) : Prop :=
  ∀ (i : Fin Γ.genus) (x : Jacobian Γ), Φ.induced x i = Ψ.induced x i

/-- The **congruence kernel relation**: pairs of correspondences whose
    induced Jacobian actions are identical. -/
def CongruenceRel (Φ Ψ : HarmonicCorr Γ) : Prop := Φ.induced = Ψ.induced


/-! ## §7 Main Theorem A: Finite Extremal Jacobian Reconstruction

Two harmonic correspondences whose induced maps agree on all `g` coordinate
valuation characters must have equal induced maps. -/


/-! ## §8 Main Theorem B: Harmonic Correspondence Rigidity

Equal induced Jacobian actions force principal equivalence, via tropical
matrix rigidity (`tropMat_determined_by_action`). -/


/-! ## §9 Master Theorem: Compressed Data Recovers Correspondence -/


/-! ## §10 Congruence Kernel Theory -/





/-! ## §11 Concrete Instantiation and Verification -/

/-- A concrete tropical curve of genus 3 (e.g., the theta graph). -/
def thetaCurve : TropicalCurveData := ⟨3, by omega⟩

/-- Two concrete correspondences on the theta curve with the same matrix. -/
def exCorr1 : HarmonicCorr thetaCurve :=
  ⟨!![1, 2, 3; 4, 5, 6; 7, 8, 9], 2⟩

def exCorr2 : HarmonicCorr thetaCurve :=
  ⟨!![1, 2, 3; 4, 5, 6; 7, 8, 9], 5⟩


/-- A correspondence with a different matrix is NOT principally equivalent. -/
def exCorr3 : HarmonicCorr thetaCurve :=
  ⟨!![1, 2, 3; 4, 5, 6; 7, 8, 0], 2⟩


/-! ## §12 Tropical Period Pairing and Nondegeneracy

A tropical period pairing is a bilinear form on the Jacobian capturing
intersection-theoretic data. Nondegeneracy of this pairing is the
condition ensuring faithfulness of the Jacobian action. -/

/-- A **tropical period pairing** on the Jacobian. -/
structure TropicalPeriodPairing (Γ : TropicalCurveData) where
  /-- The pairing matrix -/
  pairingMatrix : Fin Γ.genus → Fin Γ.genus → ℤ


/-- A tropical period pairing is **nondegenerate** if the induced linear map
    from the Jacobian to its dual is injective. -/
def NondegeneratePolarization (P : TropicalPeriodPairing Γ) : Prop :=
  Function.Injective (fun x : Jacobian Γ => fun i : Fin Γ.genus =>
    ∑ j, P.pairingMatrix i j * x j)


/-! ## §13 Existence of Reconstruction Witnesses -/

/-- **Compressed spectral data** for a correspondence. -/
structure CompressedSpectralData (Γ : TropicalCurveData) where
  /-- The spectral fingerprint: values of the induced map on test vectors -/
  fingerprint : Fin Γ.genus → Fin Γ.genus → ℤ

/-- A correspondence **realizes** compressed data if its matrix equals
    the fingerprint. -/
def RealizesCompressedData (d : CompressedSpectralData Γ) (Φ : HarmonicCorr Γ) : Prop :=
  Φ.matrix = d.fingerprint



/-! ## §14 Tropical Min-Plus Spectral Bound

We establish that the number of evaluations needed to reconstruct a
correspondence is exactly `g²`, matching the matrix dimension. -/



end TropicalIsogenyRigidity


