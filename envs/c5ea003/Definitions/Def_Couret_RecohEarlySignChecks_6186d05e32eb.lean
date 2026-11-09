-- Prove2me | Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb
-- name    : Couret_RecohEarlySignChecks_6186d05e32eb
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:07:52.43664+00:00
-- url     : https://prove2.me/theorems/6b05c4d5-d8bf-4525-a3c6-9bd7d9a937e0
-- title:
--   Early exact reading checks before translation recovery
-- statement:
--   Defines a finite-bank precheck with a binary block accepting a reading or its negative and a ternary block requiring the unchanged reading. Combines this with a sparse square check, then defines a prepared decoder that performs these checks on representatives before recovering a translation and applying the full coefficient observation check. This specifies typed Lean operations, not external parsing or cache execution.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohEarlySignChecks.lean; source file SHA-256 00fb65070ccab4cd5989c9c3480f6d3636115ad405abb34a8abb30e6f72a9c7f

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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5

set_option autoImplicit false

/-!
Early rejection of incompatible binary and ternary readings.

The bank index is J ⊕ K.  The intended cyclic bank uses prime two on J and
prime three on K.  The executable tests retain the supplied prime parameters;
their correctness uses explicit primary-representation contracts and the two
roles on G[2]: signs on J, trivial character values on K.

Binary observations must equal the representative reading or its negative;
ternary observations must equal the representative reading.  These are exact
integer-coefficient comparisons.  A final accepted recovered support always
passes these early tests, without nonvanishing or cardinality assumptions.
Combining them with the early square check therefore preserves the answer of
the full coefficient backend.  This proves an order of typed mathematical
operations, not the external Python parser, cache, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G J K : Type*} [AddCommGroup G] [DecidableEq G]
variable [Fintype J] [Fintype K]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- The binary block accepts the base reading or its negative.  The
ternary block accepts exactly the base reading. -/
def recohEarlyReadingsCheck (p k : J ⊕ K → ℕ)
    (enc : J ⊕ K → Finset G → List ℕ) (obsTerms : J ⊕ K → RecohSparseTerms)
    (B : Finset G) : Bool :=
  decide (∀ j : J,
    recohCoefficientMatch (p (Sum.inl j)) (k (Sum.inl j))
      (enc (Sum.inl j) B) (obsTerms (Sum.inl j)) = true ∨
    recohCoefficientMatchNeg (p (Sum.inl j)) (k (Sum.inl j))
      (enc (Sum.inl j) B) (obsTerms (Sum.inl j)) = true) &&
  decide (∀ j : K,
    recohCoefficientMatch (p (Sum.inr j)) (k (Sum.inr j))
      (enc (Sum.inr j) B) (obsTerms (Sum.inr j)) = true)







/-- Square and reading checks performed on the representative, before
constructing its recovered translation. -/
def recohEarlyCandidateCheck (U : Finset G) (R : G → ℕ)
    (p k : J ⊕ K → ℕ) (enc : J ⊕ K → Finset G → List ℕ)
    (obsTerms : J ⊕ K → RecohSparseTerms) (B : Finset G) : Bool :=
  recohSparseSquareCheck U B R && recohEarlyReadingsCheck p k enc obsTerms B

/-- Typed control flow with early square, binary-sign and ternary tests,
followed by direct recovery and the independent full final check. -/
def recohEarlyCoefficientBackendDecoder
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (e : H₂ ≃+ (J → ZMod 2)) (p k : J ⊕ K → ℕ)
    (enc : J ⊕ K → Finset G → List ℕ) (obsTerms : J ⊕ K → RecohSparseTerms) :
    Finset (Finset G) :=
  recohPreparedFastDecoder U half
    (recohIndexedRecoverSupport e (recohCoefficientSignBools Sum.inl p k enc obsTerms))
    (recohEarlyCandidateCheck U R p k enc obsTerms)
    (recohCoefficientObservationCheck U R p k enc obsTerms)





end Couret.STROBO2TORS


