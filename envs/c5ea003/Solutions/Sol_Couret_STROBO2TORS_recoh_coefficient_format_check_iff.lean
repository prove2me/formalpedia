-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_coefficient_format_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:00.78075+00:00
-- url     : https://prove2.me/submissions/890db4a8-826f-4428-ba0b-8e815dcea491

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









theorem p2m_local_recoh_coefficient_format_check_iff (p k : ℕ) (terms : RecohSparseTerms) :
    recohCoefficientFormatCheck p k terms = true ↔ RecohCoefficientFormat p k terms := by
  simp only [recohCoefficientFormatCheck, decide_eq_true_eq]



























variable {G : Type*} [AddCommGroup G] [DecidableEq G]













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

theorem solution : ∀ (p k : Nat) (terms : Couret.STROBO2TORS.RecohSparseTerms),
  Iff (@Eq.{1} Bool (Couret.STROBO2TORS.recohCoefficientFormatCheck p k terms) Bool.true)
    (Couret.STROBO2TORS.RecohCoefficientFormat p k terms) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_coefficient_format_check_iff

