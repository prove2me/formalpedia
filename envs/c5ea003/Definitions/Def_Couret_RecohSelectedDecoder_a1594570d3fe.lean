-- Prove2me | Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
-- name    : Couret_RecohSelectedDecoder_a1594570d3fe
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:41.780001+00:00
-- url     : https://prove2.me/theorems/6159816f-9c1e-49d0-822d-38660b6c5c89
-- title:
--   Square-selected coefficient bank and guarded decoder
-- statement:
--   For products of cyclic groups ZMod(q i) with nonzero moduli, defines a ternary measurement slot as the subtype of primary ternary coordinates equal to the square selector result. Its explicit Fintype instance evaluates that selector once: none gives an empty enumeration, and some i gives the singleton containing i. This subtype is subsingleton. The full bank index is all even-coordinate binary slots plus this selected ternary slot; prime, depth, exponent encoding, complex root and additive character are supplied for each slot. The coefficient core invokes the existing finite coefficient backend with the typed square, product-half operation and two-torsion coordinates. Typed observation pairs the square function with coefficient readings. Input format requires all q i≥2, product of moduli at least three, the typed-square format and every selected coefficient format; the Boolean check mirrors these conditions. The public decoder returns the coefficient core on a successful check and the empty set otherwise. No ternary slot is present when the selector returns none.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSelectedDecoder.lean; source file SHA-256 9df6959d546259a3037e3c1d20bf5d4697a947811925e34ec7c4b4ec93c577b0

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
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497

set_option autoImplicit false

/-!
The typed coefficient decoder with all binary coordinates and at most one
ternary coordinate selected from the labelled square. The square selector
runs before observed character coefficients are supplied. Its exact integer
backend retains the previously certified half-sum and sign-recovery code.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Only the coordinate returned by the square selector can have a ternary
measurement slot. The subtype is empty when the selector returns none. -/
abbrev RecohSelectedTernaryIndex
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :=
  {i : RecohPrimaryCoordinate q 3 // recohSquareTernaryChoice q entries = some i}

/-- Enumerate the selected ternary slot by one execution of the selector. -/
instance recohSelectedTernaryFintype
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Fintype (RecohSelectedTernaryIndex q entries) :=
  match h : recohSquareTernaryChoice q entries with
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

/-- The actual measurement interface, determined from the square alone. -/
abbrev RecohSelectedBankIndex
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :=
  RecohEvenCoordinate q ⊕ RecohSelectedTernaryIndex q entries

instance recohSelectedTernarySubsingleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Subsingleton (RecohSelectedTernaryIndex q entries) :=
  ⟨fun a b => Subtype.ext (Option.some.inj (a.property.symm.trans b.property))⟩







def recohSelectedBankPrime
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohSelectedBankIndex q entries → ℕ := Sum.elim (fun _ => 2) (fun _ => 3)

def recohSelectedBankDepth
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohSelectedBankIndex q entries → ℕ :=
  Sum.elim (fun i => (recohCanonicalPrimaryData q 2).exponent i)
    (fun i => (recohCanonicalPrimaryData q 3).exponent i.val)

def recohSelectedBankEncoding
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohSelectedBankIndex q entries → Finset ((i : Fin d) → ZMod (q i)) → List ℕ :=
  Sum.elim (fun i => recohCyclicExponents q i.val)
    (fun i => recohCyclicExponents q i.val.val)

noncomputable def recohSelectedBankRoot
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohSelectedBankIndex q entries → ℂ :=
  Sum.elim
    (fun i => recohCyclicRoot (2 ^ ((recohCanonicalPrimaryData q 2).exponent i + 1)))
    (fun i => recohCyclicRoot (3 ^ ((recohCanonicalPrimaryData q 3).exponent i.val + 1)))

noncomputable def recohSelectedObservedBank
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohSelectedBankIndex q entries → AddChar ((i : Fin d) → ZMod (q i)) ℂ :=
  Sum.elim (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2))
    (fun i => recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) i.val)











/-- The executable backend consumes only the selected coefficient slots. -/
def recohSelectedCoefficientCore
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  recohCoefficientBackendDecoder
    (recohTypedSquareSupport entries) (recohTypedSquareValue entries)
    (recohProductHalf q) Sum.inl (recohProductTwoCoordinates q)
    (recohSelectedBankPrime q entries) (recohSelectedBankDepth q entries)
    (recohSelectedBankEncoding q entries) terms

noncomputable def recohSelectedTypedObservation
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms) :=
  (recohTypedSquareValue entries,
    fun i => recohCoefficientValue (recohSelectedBankRoot q entries i) (terms i))



/-- Shape and arithmetic validation for the selected observation. -/
def RecohSelectedInputFormat
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms) : Prop :=
  (∀ i, 2 ≤ q i) ∧ 3 ≤ ∏ i, q i ∧ RecohTypedSquareFormat entries ∧
    ∀ i, RecohCoefficientFormat
      (recohSelectedBankPrime q entries i) (recohSelectedBankDepth q entries i) (terms i)

def recohSelectedInputCheck
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms) : Bool :=
  decide (∀ i, 2 ≤ q i) && decide (3 ≤ ∏ i, q i) &&
    recohTypedSquareFormatCheck entries &&
    recohAllCoefficientFormats
      (recohSelectedBankPrime q entries) (recohSelectedBankDepth q entries) terms



def recohSelectedCoefficientDecoder
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  if recohSelectedInputCheck q entries terms then recohSelectedCoefficientCore q entries terms
  else ∅













end Couret.STROBO2TORS


