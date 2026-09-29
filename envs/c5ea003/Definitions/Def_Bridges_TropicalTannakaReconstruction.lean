-- Prove2me | Definitions.Def_Bridges_TropicalTannakaReconstruction
-- name    : Bridges_TropicalTannakaReconstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:23.223146+00:00
-- url     : https://prove2.me/theorems/3f824d9a-48c2-43c3-bad8-e1656a8b41be
-- title:
--   Aether Catalog definitions — Bridges_TropicalTannakaReconstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalTannakaReconstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalTannakaReconstruction.lean by skeleton subtraction
import Mathlib
/-
# Tropical Tannaka Reconstruction via Idempotent Fiber Functors

This file formalizes a tropical/idempotent analogue of Tannaka reconstruction
for finitely generated semiring-linear categories equipped with fiber functors
into tropical semimodules.

## Main Results

* `SymmetrySemiring` — The reconstructed symmetry semiring
* `canonicalRep` — Canonical representation of each generator
* `tannaka_reconstruction` — Main reconstruction theorem
* `tannaka_functorial` — Functoriality via pullback ring homomorphisms
* `tannaka_certified` — Certified algorithmic reconstruction
* `closureCharacter_addHom` — Closure-Koopman bridge character
* `pullback_id`, `pullback_comp` — Functoriality laws
* `isNatural_zero`, `isNatural_one`, `isNatural_add` — Naturality subsemiring
* `symmetry_idem` — Idempotent specialization
-/


set_option maxHeartbeats 800000

universe u

/-! ## Section 1: Finite Closure Tensor Category -/

/-- A finitely generated tensor category presented by generators and morphisms,
    with a built-in fiber functor into tropical semimodules over S. -/
structure TensorCatData (S : Type u) [CommSemiring S] where
  /-- Number of generator objects -/
  nGen : ℕ
  /-- Fiber dimension of each generator -/
  dim : Fin nGen → ℕ
  /-- Positive dimensions -/
  dim_pos : ∀ i, 0 < dim i
  /-- Number of morphism generators -/
  nMor : ℕ
  /-- Source of each morphism generator -/
  src : Fin nMor → Fin nGen
  /-- Target of each morphism generator -/
  tgt : Fin nMor → Fin nGen
  /-- Tropical matrix of each morphism generator -/
  mat : (k : Fin nMor) → Fin (dim (tgt k)) → Fin (dim (src k)) → S

/-- Observable data for closure separation. -/
structure ObsData (S : Type u) [CommSemiring S] (C : TensorCatData S) where
  /-- Number of observables -/
  nObs : ℕ
  /-- Generator each observable lives on -/
  obsAt : Fin nObs → Fin C.nGen
  /-- Observable matrix -/
  obsMat : (j : Fin nObs) → Fin (C.dim (obsAt j)) → Fin (C.dim (obsAt j)) → S

/-- Faithfulness: HEq-equal matrices imply equal morphism indices. -/
def Faithful {S : Type u} [CommSemiring S] {C : TensorCatData S}
    (_ : ObsData S C) : Prop :=
  ∀ i j : Fin C.nMor, C.src i = C.src j → C.tgt i = C.tgt j →
    HEq (C.mat i) (C.mat j) → i = j

/-- Closure separation. -/
structure Separating {S : Type u} [CommSemiring S] {C : TensorCatData S}
    (O : ObsData S C) : Prop where
  sep : Faithful O

/-- Generator duality. -/
structure Dualizable {S : Type u} [CommSemiring S] (C : TensorCatData S) : Prop where
  pos : ∀ i, 0 < C.dim i

/-! ## Section 2: The Symmetry Semiring -/

/-- The symmetry semiring: families of endomorphism functions on generators.
    Inherits pointwise `CommSemiring` from Pi instances. -/
def SymmetrySemiring (S : Type u) [CommSemiring S] (C : TensorCatData S) :=
  (i : Fin C.nGen) → Fin (C.dim i) → Fin (C.dim i) → S

namespace SymmetrySemiring

variable {S : Type u} [CommSemiring S] {C : TensorCatData S}

instance instCommSemiring : CommSemiring (SymmetrySemiring S C) :=
  Pi.commSemiring






end SymmetrySemiring

/-! ## Section 3: Tropical Representations -/

/-- A tropical representation of a commutative semiring A over S. -/
structure TropRep (S : Type u) [CommSemiring S]
    (A : Type u) [CommSemiring A] where
  /-- Dimension -/
  rdim : ℕ
  /-- Action as a ring homomorphism -/
  act : A →+* (Fin rdim → Fin rdim → S)

/-! ## Section 4: Canonical Representation -/

/-- The canonical representation: projects to the i-th generator component. -/
def canonicalRep {S : Type u} [CommSemiring S]
    (C : TensorCatData S) (i : Fin C.nGen) :
    TropRep S (SymmetrySemiring S C) where
  rdim := C.dim i
  act := Pi.evalRingHom _ i



/-! ## Section 5: Main Reconstruction Theorem -/


/-! ## Section 6: Functoriality -/

/-- Morphism between tensor category data. -/
structure TensorCatMor {S : Type u} [CommSemiring S]
    (C D : TensorCatData S) where
  onGen : Fin C.nGen → Fin D.nGen
  dimEq : ∀ i, C.dim i = D.dim (onGen i)

/-- Pullback of an endomorphism family along a morphism. -/
def pullback {S : Type u} [CommSemiring S]
    {C D : TensorCatData S} (Φ : TensorCatMor C D) :
    SymmetrySemiring S D → SymmetrySemiring S C :=
  fun η i r c =>
    η (Φ.onGen i) (Fin.cast (by rw [Φ.dimEq]) r) (Fin.cast (by rw [Φ.dimEq]) c)

theorem pullback_zero {S : Type u} [CommSemiring S]
    {C D : TensorCatData S} (Φ : TensorCatMor C D) :
    pullback Φ (0 : SymmetrySemiring S D) = 0 := by
  funext i r c; rfl

theorem pullback_one {S : Type u} [CommSemiring S]
    {C D : TensorCatData S} (Φ : TensorCatMor C D) :
    pullback Φ (1 : SymmetrySemiring S D) = 1 := by
  funext i r c; rfl

theorem pullback_add {S : Type u} [CommSemiring S]
    {C D : TensorCatData S} (Φ : TensorCatMor C D)
    (η μ : SymmetrySemiring S D) :
    pullback Φ (η + μ) = pullback Φ η + pullback Φ μ := by
  funext i r c; rfl

theorem pullback_mul {S : Type u} [CommSemiring S]
    {C D : TensorCatData S} (Φ : TensorCatMor C D)
    (η μ : SymmetrySemiring S D) :
    pullback Φ (η * μ) = pullback Φ η * pullback Φ μ := by
  funext i r c; rfl

/-- Pullback as a ring homomorphism. -/
def pullbackHom {S : Type u} [CommSemiring S]
    {C D : TensorCatData S} (Φ : TensorCatMor C D) :
    SymmetrySemiring S D →+* SymmetrySemiring S C where
  toFun := pullback Φ
  map_zero' := pullback_zero Φ
  map_one' := pullback_one Φ
  map_add' := pullback_add Φ
  map_mul' := pullback_mul Φ


/-! ## Section 7: Identity and Composition Functoriality -/

def TensorCatMor.id {S : Type u} [CommSemiring S]
    (C : TensorCatData S) : TensorCatMor C C where
  onGen := _root_.id
  dimEq := fun _ => rfl

def TensorCatMor.comp {S : Type u} [CommSemiring S]
    {C D E : TensorCatData S}
    (Ψ : TensorCatMor D E) (Φ : TensorCatMor C D) :
    TensorCatMor C E where
  onGen := Ψ.onGen ∘ Φ.onGen
  dimEq := fun i => by rw [Function.comp, Φ.dimEq, Ψ.dimEq]



/-! ## Section 8: Certified Algorithmic Reconstruction -/


/-! ## Section 9: Closure-Koopman Bridge -/

/-- Trace functional. -/
def tropTrace {S : Type u} [CommSemiring S] {n : ℕ}
    (M : Fin n → Fin n → S) : S :=
  Finset.sum Finset.univ fun i => M i i

/-- Closure character: traces on each generator component. -/
def closureCharacter {S : Type u} [CommSemiring S] {C : TensorCatData S}
    (η : SymmetrySemiring S C) : Fin C.nGen → S :=
  fun i => tropTrace (η i)





/-! ## Section 10: Idempotent Specialization -/



/-! ## Section 11: Naturality Subsemiring -/

/-- Naturality condition: η commutes with each morphism generator
    under matrix-style composition. -/
def IsNatural {S : Type u} [CommSemiring S] {C : TensorCatData S}
    (η : SymmetrySemiring S C) : Prop :=
  ∀ (k : Fin C.nMor)
    (r : Fin (C.dim (C.tgt k))) (c : Fin (C.dim (C.src k))),
    Finset.sum Finset.univ (fun j => η (C.tgt k) r j * C.mat k j c) =
    Finset.sum Finset.univ (fun j => C.mat k r j * η (C.src k) j c)



/-- The set of natural endomorphisms. -/
def NaturalEndSet {S : Type u} [CommSemiring S]
    {C : TensorCatData S} : Set (SymmetrySemiring S C) :=
  {η | IsNatural η}



/-! ## Section 12: Concrete Example -/

/-- Two-generator example over ℕ: dim 1 and dim 2, no morphisms. -/
def exData : TensorCatData ℕ where
  nGen := 2
  dim := ![1, 2]
  dim_pos := by intro ⟨i, hi⟩; interval_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  nMor := 0
  src := Fin.elim0
  tgt := Fin.elim0
  mat := fun i => Fin.elim0 i


/-! ## Section 13: Reconstruction Record -/

/-- Complete reconstruction output. -/
structure ReconOutput (S : Type u) [CommSemiring S] (C : TensorCatData S) where
  A : Type u
  inst : CommSemiring A
  reps : Fin C.nGen → @TropRep S _ A inst
  dims : ∀ i, (reps i).rdim = C.dim i

/-- Construct the output. -/
def reconstruct {S : Type u} [CommSemiring S]
    (C : TensorCatData S) : ReconOutput S C where
  A := SymmetrySemiring S C
  inst := inferInstance
  reps := canonicalRep C
  dims := fun _ => rfl


