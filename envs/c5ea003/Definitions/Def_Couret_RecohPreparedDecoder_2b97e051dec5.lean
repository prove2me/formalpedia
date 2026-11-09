-- Prove2me | Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5
-- name    : Couret_RecohPreparedDecoder_2b97e051dec5
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:06:39.688957+00:00
-- url     : https://prove2.me/theorems/3961227d-ac9d-4f73-9008-fb3670f2b592
-- title:
--   Candidate preparation before translation recovery
-- statement:
--   Prepared edge sets filter feasible edge candidates by a Boolean precheck before decoding and recovery. The prepared candidate and final decoder constructions then apply the recovery map and full check. The coefficient variant supplies these checks from sparse observations. Correctness theorems require the precheck to be necessary for eventual acceptance; arbitrary prechecks remain valid raw inputs.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPreparedDecoder.lean; source file SHA-256 f6373eabc2c71ec81235339b571dd8d279e57b6848a6d8ac04fcaaf979efd104

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
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8

set_option autoImplicit false

/-!
Move the square test before sign recovery, as in Python `_prepare_square`.

The generic prepared decoder filters the chosen representatives before
recovery and retains the complete final checker after recovery.  The two
orders give the same answer whenever a final acceptance implies acceptance
of the representative by the precheck.  For the square test, this implication
follows from invariance under every two-torsion translation, for all finite
supports.  The resulting coefficient backend is therefore equal to the
previously certified backend, under the same support-coverage contract.

This module certifies an order of mathematical operations.  It does not
certify the separate Python cache, parser, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Feasible edge sets whose chosen representative passes the early test. -/
def recohPreparedEdgeSets (U : Finset G) (half : G → Option G)
    (precheck : Finset G → Bool) : Finset (Finset G) :=
  (recohFeasibleEdgeSets U half).filter
    (fun E => precheck (recohEdgeRepresentative half E) = true)

/-- Recover only representatives retained by the early test. -/
def recohPreparedFastCandidates (U : Finset G) (half : G → Option G)
    (recover : Finset G → Finset G) (precheck : Finset G → Bool) :
    Finset (Finset G) :=
  (recohPreparedEdgeSets U half precheck).image
    (fun E => recover (recohEdgeRepresentative half E))

/-- Early representative filtering followed by recovery and the full final
check.  The decoder still constructs at most one support per edge set. -/
def recohPreparedFastDecoder (U : Finset G) (half : G → Option G)
    (recover : Finset G → Finset G) (precheck check : Finset G → Bool) :
    Finset (Finset G) :=
  (recohPreparedFastCandidates U half recover precheck).filter
    (fun S => check S = true)









/-- Translating any finite support by two-torsion preserves its full
ordered square, without any cardinality-three assumption. -/
theorem recoh_ordered_square_two_torsion_translate (B : Finset G) (u : G)
    (hu : u + u = 0) : orderedSquare (translateSupport B u) = orderedSquare B := by
  funext z
  have hinj : ∀ x ∈ B, ∀ y ∈ B, (fun a : G => a + u) x =
      (fun a : G => a + u) y → x = y :=
    fun _ _ _ _ h => add_right_cancel h
  unfold orderedSquare translateSupport
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro y _
  rw [pair_sum_translate x y u hu]



variable {J : Type*}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable {I : Type*} [Fintype I]

/-- The coefficient decoder with the square checked before recovery, and
with the complete observation checked again after recovery. -/
def recohPreparedCoefficientBackendDecoder
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (p k : I → ℕ) (enc : I → Finset G → List ℕ)
    (obsTerms : I → RecohSparseTerms) : Finset (Finset G) :=
  recohPreparedFastDecoder U half
    (recohIndexedRecoverSupport e (recohCoefficientSignBools index p k enc obsTerms))
    (fun B => recohSparseSquareCheck U B R)
    (recohCoefficientObservationCheck U R p k enc obsTerms)





end Couret.STROBO2TORS


