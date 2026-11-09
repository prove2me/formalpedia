-- Prove2me | Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae
-- name    : Couret_RecohParityDedupTransport_fd9d6ec554ae
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:15:59.432243+00:00
-- url     : https://prove2.me/theorems/18b27361-b981-4e3e-a69a-0a6dcff63002
-- title:
--   Parity-selected decoding after anchored orbit deduplication
-- statement:
--   This defines the selected parity candidate pipeline on a supplied list of parity representatives: deduplicate that list using anchored orbit checks, pass to its finite set, recover each support using coefficient-derived binary signs, and apply the complete coefficient observation check.
--
--   The checked decoder additionally validates parity-selected typed input and returns the empty set on failure. These interfaces connect optimized orbit representatives to the same exact observation problem.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityDedupTransport.lean; source file SHA-256 dd13e6ade9a021706d0ec14fbcbb837eac41d9018980c650ddd694417386b379

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
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06

set_option autoImplicit false

/-!
Transport through the explicit anchored deduplication model.

An enumeration and an anchor remain explicit inputs with representation
contracts. The decoder really recovers from the retained representatives.
The fibre classification bounds their number by two, without assuming that
the supplied square data are realizable. No Python list-order or JSON
equivalence is claimed by this module.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











section CyclicSelected

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Recover using only the retained representatives, not the raw parity
family and not the historical edge enumeration. -/
def recohParityDedupSelectedCandidates
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i))) :=
  (recohAnchoredOrbitDedup anchor xs).toFinset.image
    (recohIndexedRecoverSupport (recohProductTwoCoordinates q)
      (recohCoefficientSignBools Sum.inl (recohParitySelectedBankPrime q entries)
        (recohParitySelectedBankDepth q entries)
        (recohParitySelectedBankEncoding q entries) terms))

def recohParityDedupSelectedCore
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i))) :=
  (recohParityDedupSelectedCandidates q entries terms xs anchor).filter
    (fun S => recohCoefficientObservationCheck (recohSelectedSquareSupport q entries)
      (recohTypedSquareValue entries) (recohParitySelectedBankPrime q entries)
      (recohParitySelectedBankDepth q entries)
      (recohParitySelectedBankEncoding q entries) terms S = true)

def recohParityDedupSelectedDecoder
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i))) :=
  if recohParitySelectedInputCheck q entries terms then
    recohParityDedupSelectedCore q entries terms xs anchor else ∅















end CyclicSelected

end Couret.STROBO2TORS


