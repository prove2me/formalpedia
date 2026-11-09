-- Prove2me | Definitions.Def_Couret_RecohCanonicalOverlap_0d3ff2cb7fda
-- name    : Couret_RecohCanonicalOverlap_0d3ff2cb7fda
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:17:01.525241+00:00
-- url     : https://prove2.me/theorems/77c826b9-f372-4e94-8bde-72b1ac9b3467
-- title:
--   Canonical coefficient tests for sign overlap
-- statement:
--   Defines a literal finite-bank sign-overlap test accepting equality or coefficient-list negation coordinatewise, and the increasing-index pairs of a list that pass a supplied overlap test. For products of cyclic groups it forms canonical primary-root coefficient terms and specializes overlap to the even-coordinate character bank.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCanonicalOverlap.lean; source file SHA-256 34c58356d945f0f3efe34a028d955ccf56a0259547dabde0e382eaaeb03b7fe5

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
import Mathlib.Data.Finset.Sort
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
import Definitions.Def_Couret_RecohCanonicalCoefficients_7eb0bfadc07d
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae

set_option autoImplicit false

/-!
Literal canonical coefficient comparisons and the binary overlap filter.

This module proves the typed mathematical meaning of Python v0.2's
`_two_overlaps`.  It does not formalize Python execution, tuple/list parsing,
the implementation of `combinations`, exceptions, or JSON serialization.
-/

namespace Couret.STROBO2TORS

section SignOrbits

variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2





end SignOrbits

section LiteralComparison

variable {I : Type*} [Fintype I]

/-- The all-coordinate comparison used by `_two_overlaps`, with literal
equality of canonical integer lists and coefficientwise negation. -/
def recohLiteralSignOverlap (left right : I → RecohSparseTerms) : Bool :=
  decide (∀ i, left i = right i ∨ left i = recohNegateTerms (right i))



end LiteralComparison

section IndexedPairs

variable {A : Type*}

/-- Index pairs in increasing order, without enumerating a translation
orbit.  This is the extensional set of pairs considered by `combinations`. -/
def recohOverlapIndexPairs (xs : List A) (overlap : A → A → Bool) :
    Finset (Fin xs.length × Fin xs.length) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ overlap xs[ij.1] xs[ij.2] = true)







end IndexedPairs

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Sorted, combined, nonzero coefficients for the canonical coordinate
character.  Its primary depth is the canonical factorization depth. -/
def recohCanonicalPrimaryTerms (p : ℕ) [Fact p.Prime]
    (i : RecohPrimaryCoordinate q p)
    (S : Finset ((j : Fin d) → ZMod (q j))) : RecohSparseTerms :=
  recohCanonicalRootTerms p ((recohCanonicalPrimaryData q p).exponent i)
    (recohCyclicExponents q i.val S)









/-- Literal all-coordinate comparison, with the same equality/negation
predicate as the typed mathematical content of `_two_overlaps`. -/
def recohCanonicalTwoOverlap
    (S T : Finset ((j : Fin d) → ZMod (q j))) : Bool :=
  recohLiteralSignOverlap (fun i : RecohEvenCoordinate q => recohCanonicalPrimaryTerms q 2 i S)
    (fun i : RecohEvenCoordinate q => recohCanonicalPrimaryTerms q 2 i T)











end Cyclic

end Couret.STROBO2TORS


