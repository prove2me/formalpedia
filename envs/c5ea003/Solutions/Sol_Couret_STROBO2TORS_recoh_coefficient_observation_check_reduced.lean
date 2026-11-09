-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_coefficient_observation_check_reduced
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:13.901246+00:00
-- url     : https://prove2.me/submissions/dc3c2ca4-ae09-4355-ba9d-e0554b51d8e1

import Aesop
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
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
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Exact observation checking from integer cyclotomic coefficients.

Observed readings are supplied directly as lists of pairs `(exponent,
integer coefficient)`.  No conversion from coefficients back to root lists
is used.  Complex values occur only in the interpretation and correctness
theorems; all checkers compare natural numbers and integer coefficients.

The range contract is sufficient for faithful evaluation.  The stronger
typed-format contract also excludes zero coefficients and repeated
exponents, matching the conditions inspected by Python `_read_coefficients`.
It does not certify JSON parsing, Python execution or sorting.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators





































variable {G : Type*} [AddCommGroup G] [DecidableEq G]









omit [AddCommGroup G] [DecidableEq G] in
/-- The coefficient checker specializes exactly to the previous
root-list checker when the observed coefficients are their raw reduction. -/
theorem recoh_coefficient_readings_check_reduced {m : ℕ} (p k : Fin m → ℕ)
    (enc : Fin m → Finset G → List ℕ) (obsExp : Fin m → List ℕ) (S : Finset G) :
    recohCoefficientReadingsCheck p k enc
      (fun i => recohReducedTerms (p i) (k i) (obsExp i)) S =
      recohSparseReadingsCheck p k enc obsExp S := by
  apply Bool.eq_iff_iff.mpr
  simp only [recohCoefficientReadingsCheck, recohCoefficientMatch,
    recohSparseReadingsCheck, decide_eq_true_eq]

theorem p2m_local_recoh_coefficient_observation_check_reduced {m : ℕ}
    (U : Finset G) (R : G → ℕ) (p k : Fin m → ℕ)
    (enc : Fin m → Finset G → List ℕ) (obsExp : Fin m → List ℕ) (S : Finset G) :
    recohCoefficientObservationCheck U R p k enc
      (fun i => recohReducedTerms (p i) (k i) (obsExp i)) S =
      recohSparseObservationCheck U R p k enc obsExp S := by
  unfold recohCoefficientObservationCheck recohSparseObservationCheck
  rw [recoh_coefficient_readings_check_reduced]

/-!
The coefficient checkers do not themselves establish support coverage,
primality, primitive-root identities or the interpretation of candidate
encodings.  Their correctness theorems display these contracts explicitly.
The observed coefficient values require no witness as a sum of three roots.
Such a representation, if it exists, is supplied by a successfully checked
candidate rather than assumed as an input encoding.

Typed lists may be arbitrarily long.  No constant or bit-complexity bound
for reading or checking observed input is asserted here.  In particular,
the twelve-position bound for comparing two normalized triples is not a
bound on arbitrary externally supplied coefficient lists.
-/


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {m : Nat}
  (U : Finset.{p2m_u_0} G) (R : G → Nat) (p k : Fin m → Nat) (enc : Fin m → Finset.{p2m_u_0} G → List.{0} Nat)
  (obsExp : Fin m → List.{0} Nat) (S : Finset.{p2m_u_0} G),
  @Eq.{1} Bool
    (@Couret.STROBO2TORS.recohCoefficientObservationCheck.{p2m_u_0, 0} G inst inst_1 (Fin m) (Fin.fintype m) U R p k enc
      (fun i => Couret.STROBO2TORS.recohReducedTerms (p i) (k i) (obsExp i)) S)
    (@Couret.STROBO2TORS.recohSparseObservationCheck.{p2m_u_0} G inst inst_1 m U R p k enc obsExp S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_coefficient_observation_check_reduced

