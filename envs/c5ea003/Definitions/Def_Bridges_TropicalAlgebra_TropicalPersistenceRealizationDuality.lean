-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_TropicalPersistenceRealizationDuality
-- name    : Bridges_TropicalAlgebra_TropicalPersistenceRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:36.587989+00:00
-- url     : https://prove2.me/theorems/ec246e1b-f4bf-4e8e-9306-4ff1543f2061
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_TropicalPersistenceRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.TropicalPersistenceRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/TropicalPersistenceRealizationDuality.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Persistence Realization Duality via Idempotent Interleaving Semimodules

This file establishes a formal algebraic theory in which **finite tropical persistence data**
is classified by canonical idempotent semimodule objects, with **stable tropical observables**
represented by evaluation on those objects, and with a **certified reconstruction theorem**
recovering barcodes from finite residuation/interleaving data.

## Main results

- `admitsInterleavingAt_refl`: Interleaving is reflexive at ε = 0.
- `admitsInterleavingAt_symm`: Interleaving is symmetric.
- `admitsInterleavingAt_anti_mono`: Interleaving anti-monotone in scale (smaller ε is easier).
- `stable_func_eq_on_zero_interleaving`: Stable functionals equalize 0-interleaved elements.
- `stable_func_strong_bound`: The strong Lipschitz bound φ(x) + ε ≤ φ(y) from F ε x ≤ y.
- `stable_func_factors_through_barcode`: Every stable functional factors uniquely through
  the canonical barcode quotient (main universal factorization theorem).
- `certified_barcode_reconstruction`: Distance-zero generators get equal functional values.
- `barcode_classification`: Barcode quotient classifies generators up to stable equivalence.
- `interleaving_pseudometric_triangle`: Triangle inequality for functional values.

## Keywords

tropical persistence, barcode reconstruction, idempotent semimodule, interleaving distance,
residuation, universal representation, minimal realization, certified stability,
interpretable machine learning, persistent features, canonical quotient
-/

noncomputable section

open scoped NNReal

namespace TropicalPersistence

/-! ## Core Structures -/

/-- An interleaving action on a preordered type `M`, modeling how a persistence module
    shifts under filtration parameter changes.

    The shift map `F ε` represents inclusion from filtration level `t` to `t + ε`.
    It satisfies identity at zero, additivity of shifts, and monotonicity in scale
    (larger filtration parameters give larger images). -/
structure InterleavingAction (M : Type*) [Preorder M] where
  /-- The filtration shift map. -/
  F : ℝ≥0 → M → M
  /-- The zero shift is the identity. -/
  map_zero' : ∀ x, F 0 x = x
  /-- Shifts compose additively. -/
  map_add' : ∀ ε δ x, F (ε + δ) x = F ε (F δ x)
  /-- Monotone in the scale: larger shifts produce larger elements.
      This models the fact that including further into the filtration
      produces "more filtered" elements. -/
  mono_scale' : ∀ (x : M) (ε δ : ℝ≥0), ε ≤ δ → F ε x ≤ F δ x

/-- Two elements are **ε-interleaved** if shifting either by ε lands below the other.
    This is the certificate version of interleaving distance. -/
def AdmitsInterleavingAt {M : Type*} [Preorder M]
    (act : InterleavingAction M) (ε : ℝ≥0) (x y : M) : Prop :=
  act.F ε x ≤ y ∧ act.F ε y ≤ x

/-! ## Foundational Interleaving Lemmas -/



/-
Interleaving is anti-monotone in scale: if elements are ε-interleaved
    and δ ≤ ε, then they are δ-interleaved (smaller scale is easier to satisfy).
-/


/-! ## Tropical Persistence Functionals -/

/-- A **tropical persistence functional**: a monotone, shift-equivariant map `M → ℝ≥0`.
    These represent stable observables of persistent data.

    The shift-equivariance axiom `φ(F ε x) = φ(x) + ε` expresses that the observable
    shifts linearly with the filtration parameter, making it a "tropical linear" functional.

    The key property is that stable functionals are automatically Lipschitz with
    respect to the interleaving certificate distance. -/
structure TropPersFunc {M : Type*} [Preorder M] (act : InterleavingAction M) where
  /-- The underlying map. -/
  toFun : M → ℝ≥0
  /-- Order-preserving. -/
  mono' : ∀ {x y : M}, x ≤ y → toFun x ≤ toFun y
  /-- Shift-equivariance: `φ(F ε x) = φ(x) + ε`. -/
  shift_eq' : ∀ (ε : ℝ≥0) (x : M), toFun (act.F ε x) = toFun x + ε





/-! ## Stable Kernel and Barcode Quotient -/

/-- The **stable kernel**: two indices are equivalent if every stable functional
    assigns their generators the same value. This is the fundamental equivalence
    relation that defines the barcode quotient. -/
def stableKernel {ι M : Type*} [Preorder M]
    (act : InterleavingAction M) (gen : ι → M) (i j : ι) : Prop :=
  ∀ func : TropPersFunc act, func.toFun (gen i) = func.toFun (gen j)

/-- The stable kernel is an equivalence relation. -/
def stableKernelSetoid {ι M : Type*} [Preorder M]
    (act : InterleavingAction M) (gen : ι → M) : Setoid ι where
  r := stableKernel act gen
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h func => (h func).symm
    trans := fun h1 h2 func => (h1 func).trans (h2 func)
  }


/-! ## Barcode Quotient Type -/

/-- The **barcode quotient**: the quotient of generators by the stable kernel.
    Each equivalence class corresponds to a distinct barcode interval —
    generators that no stable functional can distinguish are collapsed. -/
def BarcodeQuotient {ι M : Type*} [Preorder M]
    (act : InterleavingAction M) (gen : ι → M) : Type _ :=
  Quotient (stableKernelSetoid act gen)

/-- The canonical projection from generators to the barcode quotient. -/
def barcodeProj {ι M : Type*} [Preorder M]
    (act : InterleavingAction M) (gen : ι → M) :
    ι → BarcodeQuotient act gen :=
  Quotient.mk (stableKernelSetoid act gen)



/-! ## Main Theorem: Universal Factorization Through Barcode Quotient -/


/-! ## Tropical Interval and Barcode Structures -/

/-- A **tropical interval** represents a birth-death pair in a barcode.
    This is the basic building block of barcode decompositions. -/
structure TropicalInterval where
  /-- Birth time of the feature. -/
  birth : ℝ≥0
  /-- Death time of the feature. -/
  death : ℝ≥0
  /-- Birth precedes death. -/
  valid : birth ≤ death

/-- The lifetime (persistence) of a tropical interval. -/
def TropicalInterval.lifetime (I : TropicalInterval) : ℝ≥0 :=
  I.death - I.birth




/-! ## Finite Interleaving Presentations -/

/-- A **finite interleaving presentation**: a finite generating family with
    pairwise interleaving certificate distances.

    This structure captures the finite input data from which barcodes can be
    reconstructed. The distance matrix `dist i j` records the certified
    interleaving distance between generators `gen i` and `gen j`. -/
structure FinInterleavingPres {M : Type*} [Preorder M]
    (act : InterleavingAction M) (ι : Type*) [Fintype ι] where
  /-- The generating family. -/
  gen : ι → M
  /-- Pairwise interleaving certificate distance. -/
  dist : ι → ι → ℝ≥0
  /-- Distances certify interleaving: `gen i` and `gen j` are `dist i j`-interleaved. -/
  dist_certifies : ∀ i j, AdmitsInterleavingAt act (dist i j) (gen i) (gen j)
  /-- Distance is symmetric. -/
  dist_symm : ∀ i j, dist i j = dist j i
  /-- Diagonal is zero. -/
  dist_refl : ∀ i, dist i i = 0




/-! ## Classification and Representation -/



/-! ## Finiteness -/

/-- The barcode quotient of a finite generator set is finite. -/
instance barcodeQuotient_finite {ι M : Type*} [Fintype ι] [Preorder M]
    (act : InterleavingAction M) (gen : ι → M) :
    Finite (BarcodeQuotient act gen) :=
  Quotient.finite (stableKernelSetoid act gen)

/-! ## Concrete Examples -/

/-- The additive shift action on `ℝ≥0`: the canonical interleaving structure
    where `F ε x = x + ε`. -/
def additiveShiftAction : InterleavingAction ℝ≥0 where
  F ε x := x + ε
  map_zero' x := by simp
  map_add' ε δ x := by simp [add_assoc, add_comm δ]
  mono_scale' x _ _ hεδ := add_le_add_right hεδ x

/-- The identity functional on additive shift. -/
def identityFunc : TropPersFunc additiveShiftAction where
  toFun x := x
  mono' h := h
  shift_eq' _ _ := rfl


/-! ## Idempotent Laws -/


/-! ## Two-Generator Separation Example -/

/-- The product shift action on `ℝ≥0 × ℝ≥0`: componentwise additive shift. -/
def pairShiftAction : InterleavingAction (ℝ≥0 × ℝ≥0) where
  F ε p := (p.1 + ε, p.2 + ε)
  map_zero' p := by ext <;> simp
  map_add' ε δ p := by ext <;> simp [add_assoc, add_comm δ]
  mono_scale' p _ _ hεδ :=
    Prod.mk_le_mk.mpr ⟨add_le_add_right hεδ p.1, add_le_add_right hεδ p.2⟩

/-- First coordinate projection is a stable functional on the pair action. -/
def fstFunc : TropPersFunc pairShiftAction where
  toFun p := p.1
  mono' h := h.1
  shift_eq' _ _ := rfl



/-! ## Triangle Inequality for Functional Values -/

/-
**Triangle inequality**: if x, y are ε₁-interleaved and y, z are ε₂-interleaved,
    then the functional values satisfy φ(x) + ε₁ ≤ φ(y) and φ(y) + ε₂ ≤ φ(z),
    giving φ(x) + (ε₁ + ε₂) ≤ φ(z) + ε₂ ≤ ...
-/

/-! ## Perturbation Stability for Finite Presentations -/


/-! ## Strong Bounds for Interleaving -/




end TropicalPersistence

end


