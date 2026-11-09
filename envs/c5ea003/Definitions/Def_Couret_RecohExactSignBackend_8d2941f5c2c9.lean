-- Prove2me | Definitions.Def_Couret_RecohExactSignBackend_8d2941f5c2c9
-- name    : Couret_RecohExactSignBackend_8d2941f5c2c9
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:48.494423+00:00
-- url     : https://prove2.me/theorems/4376385b-7c31-4efc-b736-b050185b2eb9
-- title:
--   Boolean sign recovery and sparse decoding
-- statement:
--   A Boolean equality test becomes a binary sign bit, with true encoded as zero and false as one. An additive coordinate equivalence on two-torsion reconstructs the translation from these bits, then translates the candidate support. Primary sparse equality supplies executable sign tests, and the sparse backend combines sign recovery with a full observation check.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohExactSignBackend.lean; source file SHA-256 f99e3408f62032866dd7332e37aea90148e1e51601887993b2026a97b35d79dd

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
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Computable comparison bits and their refinement of complex sign recovery.

The comparison booleans are supplied by an exact arithmetic backend.  Only
their correctness proposition mentions complex numbers.  The recovered
coordinate vector and transport through a supplied coordinate equivalence
are ordinary Lean definitions, with no complex equality decision at runtime.
-/

namespace Couret.STROBO2TORS

/-- Translate the result of an exact equality test into one binary coordinate. -/
def recohSignBitFromBool (same : Bool) : ZMod 2 := if same then 0 else 1



variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Recovery from exact boolean comparisons, with the coordinate map supplied
as data.  This definition does not search the two-torsion subgroup. -/
def recohRecoverTranslationFromBools
    (e : H₂ ≃+ (Fin r → ZMod 2)) (same : Fin r → Bool) : H₂ :=
  e.symm (fun i => recohSignBitFromBool (same i))





variable [DecidableEq G]





/-- Sparse integer comparisons for the binary part of the character bank.
The observed sum is compared to the unshifted representative's sum. -/
def recohPrimarySignBools (k : Fin r → ℕ)
    (base obs : Fin r → List ℕ) : Fin r → Bool :=
  fun i => recohSparseEqual (recohReducedTerms 2 (k i) (obs i))
    (recohReducedTerms 2 (k i) (base i))



/-- Computable support recovery from exact comparison bits and a supplied
coordinate equivalence. -/
def recohBooleanRecoverSupport (e : H₂ ≃+ (Fin r → ZMod 2))
    (same : Finset G → Fin r → Bool) (B : Finset G) : Finset G :=
  translateSupport B (recohRecoverTranslationFromBools e (same B) : G)







/-- Concrete sparse sign recovery.  The exponent lists and binary coordinate
equivalence are data; complex numbers occur only in its correctness theorem. -/
def recohSparseRecoverSupport (e : H₂ ≃+ (Fin r → ZMod 2)) (k : Fin r → ℕ)
    (encode : Fin r → Finset G → List ℕ) (obsExp : Fin r → List ℕ) :
    Finset G → Finset G :=
  recohBooleanRecoverSupport e
    (fun B => recohPrimarySignBools k (fun i => encode i B) obsExp)





/-- The complete finite algorithm on supplied exact data.  Both recovery
and final filtering use integer-term comparisons.  It receives no complex
numbers, does not enumerate G or G[2], and needs no Fintype instance on G. -/
def recohSparseBackendDecoder {m : ℕ}
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (e : H₂ ≃+ (Fin r → ZMod 2)) (k2 : Fin r → ℕ)
    (enc2 : Fin r → Finset G → List ℕ) (obs2 : Fin r → List ℕ)
    (p k : Fin m → ℕ) (enc : Fin m → Finset G → List ℕ)
    (obsExp : Fin m → List ℕ) : Finset (Finset G) :=
  recohCheckedFastDecoder U half (recohSparseRecoverSupport e k2 enc2 obs2)
    (recohSparseObservationCheck U R p k enc obsExp)





end Couret.STROBO2TORS


