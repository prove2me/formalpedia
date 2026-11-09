-- Prove2me | Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
-- name    : Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:51.135218+00:00
-- url     : https://prove2.me/theorems/0adc2b6a-186b-4394-96fa-3c0d04639f09
-- title:
--   Canonical cyclic coefficient decoder
-- statement:
--   For a finite product of positive cyclic moduli, the bank includes one two-primary character at each even coordinate and one three-primary character at each three-divisible coordinate when an even factor exists. The bundle defines each index prime, depth, root and exponent encoding, the coefficient backend, and the typed observation.
--
--   Its input format requires moduli at least two, total group cardinality at least three, a square list of three to six distinct points with multiplicities one through three totaling nine and one or three odd entries, and reduced duplicate-free nonzero coefficient lists. The checked decoder returns the coefficient core on valid input and the empty set otherwise.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicCoefficientDecoder.lean; source file SHA-256 28a7b086d267426fb1e0879ed74d17a1d11a1d82cadf2b7320c0a89680767395

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
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
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An instantiated RECOH decoder on typed observations of cyclic products.

The user supplies only the moduli, labelled square entries, and the observed
coefficient lists.  The primary parameters, exponent encoders, binary
coordinates, doubling solver, square-value function and its covering set
are constructed here.  Their correctness contracts are all discharged.

There is one binary slot for every even factor. Ternary slots occur only
when some factor is even, exactly as for the fixed bank in the Python
decoder. The input guard also imposes moduli at least two, group order at
least three, and the typed numeric/uniqueness checks of its observation
readers. JSON syntax, machine execution and serialization remain separate.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Ternary measurements are used only in the presence of binary torsion. -/
abbrev RecohActiveTernaryCoordinate :=
  {i : Fin d // 3 ∣ q i ∧ ∃ j : Fin d, 2 ∣ q j}

/-- The labelled fixed bank of the external product presentation. -/
abbrev RecohCyclicBankIndex := RecohEvenCoordinate q ⊕ RecohActiveTernaryCoordinate q

/-- The prime attached to each bank slot. -/
def recohCyclicBankPrime : RecohCyclicBankIndex q → ℕ :=
  Sum.elim (fun _ => 2) (fun _ => 3)

/-- Primary exponents computed from the moduli, not supplied as contracts. -/
def recohCyclicBankDepth : RecohCyclicBankIndex q → ℕ :=
  Sum.elim
    (fun i => (recohCanonicalPrimaryData q 2).exponent i)
    (fun i => (recohCanonicalPrimaryData q 3).exponent ⟨i.val, i.property.1⟩)

/-- Actual coordinate exponents for every candidate, with multiplicities. -/
def recohCyclicBankEncoding : RecohCyclicBankIndex q →
    Finset ((i : Fin d) → ZMod (q i)) → List ℕ :=
  Sum.elim (fun i => recohCyclicExponents q i.val)
    (fun i => recohCyclicExponents q i.val)

/-- The semantic roots are determined by the primary orders. -/
noncomputable def recohCyclicBankRoot : RecohCyclicBankIndex q → ℂ :=
  Sum.elim
    (fun i => recohCyclicRoot (2 ^ ((recohCanonicalPrimaryData q 2).exponent i + 1)))
    (fun i => recohCyclicRoot
      (3 ^ ((recohCanonicalPrimaryData q 3).exponent ⟨i.val, i.property.1⟩ + 1)))

/-- The fully determined complex bank appears only in the specification. -/
noncomputable def recohCyclicObservedBank : RecohCyclicBankIndex q →
    AddChar ((i : Fin d) → ZMod (q i)) ℂ :=
  Sum.elim
    (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2))
    (fun i => recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3)
      ⟨i.val, i.property.1⟩)











/-- The algorithm before the typed input guard. All auxiliary data are
computed from the moduli and from the observed square itself. -/
def recohCyclicCoefficientCore
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  recohCoefficientBackendDecoder
    (recohTypedSquareSupport entries) (recohTypedSquareValue entries)
    (recohProductHalf q) Sum.inl (recohProductTwoCoordinates q)
    (recohCyclicBankPrime q) (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms

/-- The semantic observation represented by the typed input. -/
noncomputable def recohCyclicTypedObservation
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms) :=
  (recohTypedSquareValue entries,
    fun i => recohCoefficientValue (recohCyclicBankRoot q i) (terms i))



/-- Numeric and shape checks after the JSON values have been given their
types. The order of entries and terms is not constrained. -/
def RecohCyclicInputFormat
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms) : Prop :=
  (∀ i, 2 ≤ q i) ∧ 3 ≤ ∏ i, q i ∧ RecohTypedSquareFormat entries ∧
    ∀ i, RecohCoefficientFormat (recohCyclicBankPrime q i) (recohCyclicBankDepth q i) (terms i)

def recohCyclicInputCheck
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms) : Bool :=
  decide (∀ i, 2 ≤ q i) && decide (3 ≤ ∏ i, q i) &&
    recohTypedSquareFormatCheck entries &&
    recohAllCoefficientFormats (recohCyclicBankPrime q) (recohCyclicBankDepth q) terms



/-- Complete typed decoder with the input checks of the external format. -/
def recohCyclicCoefficientDecoder
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  if recohCyclicInputCheck q entries terms then recohCyclicCoefficientCore q entries terms
  else ∅













end Couret.STROBO2TORS


