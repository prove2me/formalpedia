-- Prove2me | Definitions.Def_Couret_RecohParityDecoder_e5701300ff06
-- name    : Couret_RecohParityDecoder_e5701300ff06
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:14:14.86109+00:00
-- url     : https://prove2.me/theorems/370705bf-3fd8-40d2-a063-831ff065bbcf
-- title:
--   Parity representatives and selected coefficient decoding
-- statement:
--   This bundle forms checked decoders from parity representatives and recovered supports. It also transports the legacy selected bank to parity-selected indices, carrying primes, depths, exponent encodings, roots and characters through the index equivalence. Typed observations, input-format checks and final coefficient decoders then use that transported bank. The construction preserves the split between candidate generation, input validation and exact checking.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDecoder.lean; source file SHA-256 9726528ae3811835f453edf79765026c8ce160b6454c01ab77b6971e40840b98

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517

set_option autoImplicit false

/-!
Coefficient decoding from the compact parity family.

The generic bridge uses a proved cover modulo two-torsion, the historical
sign-recovery specification and the exact integer observation checker.
The new candidate construction is an image of the parity family, not the
historical edge-triple enumeration. Definitions enumerate neither G nor
its two-torsion subgroup. Complex values occur only in the specification.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Recover one translated support from each member of a supplied family,
then retain exactly the supports accepted by the Boolean checker. -/
def recohRepresentativeCheckedDecoder (reps : Finset (Finset G))
    (recover : Finset G → Finset G) (check : Finset G → Bool) : Finset (Finset G) :=
  (reps.image recover).filter (fun S => check S = true)







/-- Binary equality bits recover one support from each parity representative. -/
def recohParityCoefficientCandidates
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (p k : I → ℕ) (enc : I → Finset G → List ℕ)
    (obsTerms : I → RecohSparseTerms) : Finset (Finset G) :=
  (recohParityRepresentatives U R half).image
    (recohIndexedRecoverSupport e (recohCoefficientSignBools index p k enc obsTerms))



variable [Fintype I]

/-- The compact integer-coefficient backend uses the actual parity family
and the historical, independently verified sign and observation arithmetic. -/
def recohParityCoefficientBackendDecoder
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (p k : I → ℕ) (enc : I → Finset G → List ℕ)
    (obsTerms : I → RecohSparseTerms) : Finset (Finset G) :=
  (recohParityCoefficientCandidates U R half index e p k enc obsTerms).filter
    (fun S => recohCoefficientObservationCheck U R p k enc obsTerms S = true)





section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- The optional ternary slot is computed by the parity selector itself. -/
abbrev RecohParitySelectedTernaryIndex
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :=
  {i : RecohPrimaryCoordinate q 3 // recohParityTernaryChoice q entries = some i}

/-- Enumerate the new slot by evaluating the parity selector, including the
empty-slot case; no enumeration of the ambient group is introduced. -/
instance recohParitySelectedTernaryFintype
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Fintype (RecohParitySelectedTernaryIndex q entries) :=
  match h : recohParityTernaryChoice q entries with
  | none =>
      { elems := ∅
        complete := by
          intro a
          exact (Option.some_ne_none a.val (a.property.symm.trans h)).elim }
  | some i =>
      { elems := {⟨i, h⟩}
        complete := by
          intro a
          apply Finset.mem_singleton.mpr
          apply Subtype.ext
          exact Option.some.inj (a.property.symm.trans h) }

abbrev RecohParitySelectedBankIndex
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :=
  RecohEvenCoordinate q ⊕ RecohParitySelectedTernaryIndex q entries

/-- The same labelled ternary coordinate is selected. Only its proof of
selection changes; its value and the order of coordinates do not. -/
def recohParitySelectedTernaryEquiv
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohParitySelectedTernaryIndex q entries ≃ RecohSelectedTernaryIndex q entries where
  toFun i := ⟨i.val, (recoh_parity_ternary_choice_eq_legacy q entries).symm.trans i.property⟩
  invFun i := ⟨i.val, (recoh_parity_ternary_choice_eq_legacy q entries).trans i.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def recohParitySelectedBankEquiv
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohParitySelectedBankIndex q entries ≃ RecohSelectedBankIndex q entries :=
  Equiv.sumCongr (Equiv.refl _) (recohParitySelectedTernaryEquiv q entries)

/-- Parameter and encoding maps are transported along the explicit slot
equivalence, preserving the historical arithmetic at each coordinate. -/
def recohParitySelectedBankPrime
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohParitySelectedBankIndex q entries → ℕ :=
  fun i => recohSelectedBankPrime q entries (recohParitySelectedBankEquiv q entries i)

def recohParitySelectedBankDepth
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohParitySelectedBankIndex q entries → ℕ :=
  fun i => recohSelectedBankDepth q entries (recohParitySelectedBankEquiv q entries i)

def recohParitySelectedBankEncoding
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohParitySelectedBankIndex q entries → Finset ((i : Fin d) → ZMod (q i)) → List ℕ :=
  fun i => recohSelectedBankEncoding q entries (recohParitySelectedBankEquiv q entries i)

noncomputable def recohParitySelectedBankRoot
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohParitySelectedBankIndex q entries → ℂ :=
  fun i => recohSelectedBankRoot q entries (recohParitySelectedBankEquiv q entries i)

noncomputable def recohParitySelectedObservedBank
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohParitySelectedBankIndex q entries → AddChar ((i : Fin d) → ZMod (q i)) ℂ :=
  fun i => recohSelectedObservedBank q entries (recohParitySelectedBankEquiv q entries i)

/-- Relabel the same measured integer coefficients for comparison with the
historical API. This does not request any additional measurements. -/
def recohParitySelectedLegacyTerms
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) :
    RecohSelectedBankIndex q entries → RecohSparseTerms :=
  fun i => terms ((recohParitySelectedBankEquiv q entries).symm i)









/-- The actual compact candidate family with binary sign recovery. -/
def recohParitySelectedCoefficientCandidates
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  recohParityCoefficientCandidates
    (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
    (recohProductHalf q) Sum.inl (recohProductTwoCoordinates q)
    (recohParitySelectedBankPrime q entries) (recohParitySelectedBankDepth q entries)
    (recohParitySelectedBankEncoding q entries) terms

def recohParitySelectedCoefficientCore
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  recohParityCoefficientBackendDecoder
    (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
    (recohProductHalf q) Sum.inl (recohProductTwoCoordinates q)
    (recohParitySelectedBankPrime q entries) (recohParitySelectedBankDepth q entries)
    (recohParitySelectedBankEncoding q entries) terms

noncomputable def recohParitySelectedTypedObservation
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) :=
  (recohTypedSquareValue entries,
    fun i => recohCoefficientValue (recohParitySelectedBankRoot q entries i) (terms i))









/-- Typed guards are retained, with the compact selector's measured slots.
They do not specify JSON parsing, ordering or Python exceptions. -/
def RecohParitySelectedInputFormat
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) : Prop :=
  (∀ i, 2 ≤ q i) ∧ 3 ≤ ∏ i, q i ∧ RecohTypedSquareFormat entries ∧
    ∀ i, RecohCoefficientFormat
      (recohParitySelectedBankPrime q entries i)
      (recohParitySelectedBankDepth q entries i) (terms i)

def recohParitySelectedInputCheck
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) : Bool :=
  decide (∀ i, 2 ≤ q i) && decide (3 ≤ ∏ i, q i) &&
    recohTypedSquareFormatCheck entries &&
    recohAllCoefficientFormats
      (recohParitySelectedBankPrime q entries) (recohParitySelectedBankDepth q entries) terms







def recohParitySelectedCoefficientDecoder
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  if recohParitySelectedInputCheck q entries terms then
    recohParitySelectedCoefficientCore q entries terms else ∅













end CyclicSelected

end Couret.STROBO2TORS


