-- Prove2me | Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2
-- name    : Couret_RecohSparseObservation_6dd9be0e8eb2
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:12.266573+00:00
-- url     : https://prove2.me/theorems/ce4e95a7-9672-4d0b-88c0-ec4d6dfbb023
-- title:
--   Finite sparse observation checks
-- statement:
--   Pair-sum positions enumerate where a support square can be nonzero. The square check compares a candidate against a supplied sparse support bound and count function; reading checks compare reduced sparse root sums at each bank index. Their conjunction is the sparse observation check. These Boolean operations are the finite executable counterparts of full observation equality.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSparseObservation.lean; source file SHA-256 3e5ab9ed2f77e232442c1e513ac667674b59190c499be9b6b00defed9b569878

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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Executable sparse checking of a full RECOH observation.

The ordered square is checked only on the supplied support of the observed
square together with sums of pairs in the proposed support.  Character
readings are checked by the certified integer-term comparator.  Neither
checker enumerates the ambient group or requires `Fintype G`.

The encodings of proposed and observed readings are input data.  Their
interpretation contracts, the primary orders, primitive roots and support
coverage are explicit hypotheses of correctness.  This module does not
certify a parser or construct those encodings from complex numbers.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- All group elements at which a proposed support can have a nonzero
ordered-square coefficient; no ambient enumeration is used. -/
def recohPairSumPositions (S : Finset G) : Finset G :=
  (S ×ˢ S).image (fun xy => xy.1 + xy.2)

theorem recoh_ordered_square_zero_outside_pair_sums (S : Finset G) (z : G)
    (hz : z ∉ recohPairSumPositions S) : orderedSquare S z = 0 := by
  unfold orderedSquare
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hne : x + y ≠ z := by
    intro he
    exact hz (Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, he⟩)
  simp only [if_neg hne]

/-- An executable bounded decision on the union of observed and proposed
square positions.  The supplied function `R` is evaluated only there. -/
def recohSparseSquareCheck (U S : Finset G) (R : G → ℕ) : Bool :=
  decide (∀ z ∈ U ∪ recohPairSumPositions S, orderedSquare S z = R z)

/-- Under the explicit support-coverage contract, the sparse test is
equivalent to equality of the full ordered-square functions. -/
theorem recoh_sparse_square_check_iff (U S : Finset G) (R : G → ℕ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U) :
    recohSparseSquareCheck U S R = true ↔ orderedSquare S = R := by
  simp only [recohSparseSquareCheck, decide_eq_true_eq]
  constructor
  · intro h
    funext z
    by_cases hz : z ∈ U ∪ recohPairSumPositions S
    · exact h z hz
    · have hpair : z ∉ recohPairSumPositions S := by
        intro hm
        exact hz (Finset.mem_union.mpr (Or.inr hm))
      have hrzero : R z = 0 := by
        by_contra hr
        exact hz (Finset.mem_union.mpr (Or.inl (hR z hr)))
      rw [recoh_ordered_square_zero_outside_pair_sums S z hpair, hrzero]
  · intro h z _
    exact congrFun h z

/-- All readings are checked by bounded quantification over the finite bank
index.  Its runtime data contain natural exponents, not complex numbers. -/
def recohSparseReadingsCheck {m : ℕ} (p k : Fin m → ℕ)
    (enc : Fin m → Finset G → List ℕ) (obsExp : Fin m → List ℕ)
    (S : Finset G) : Bool :=
  decide (∀ i : Fin m, recohSparseEqual
    (recohReducedTerms (p i) (k i) (enc i S))
    (recohReducedTerms (p i) (k i) (obsExp i)) = true)



/-- Executable complete observation test.  Only the finite supports, the
group operations, natural coefficients and exponent encodings are used. -/
def recohSparseObservationCheck {m : ℕ} (U : Finset G) (R : G → ℕ)
    (p k : Fin m → ℕ) (enc : Fin m → Finset G → List ℕ)
    (obsExp : Fin m → List ℕ) (S : Finset G) : Bool :=
  recohSparseSquareCheck U S R && recohSparseReadingsCheck p k enc obsExp S




end Couret.STROBO2TORS


