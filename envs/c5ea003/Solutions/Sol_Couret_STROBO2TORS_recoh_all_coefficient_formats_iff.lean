-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_all_coefficient_formats_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:32.932537+00:00
-- url     : https://prove2.me/submissions/592236d3-3f59-499f-93d9-f8d8ec9d6f1e

import Aesop
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_format_check_iff
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
Typed sparse input for the labelled ordered convolution square.

The coefficient function and its covering finite set are constructed from
the same list of position/count entries.  Their consistency is proved,
rather than supplied to the decoder.  The format validator expresses the
numeric checks performed by the Python square reader after coordinates and
integers have been parsed.  Syntactic JSON parsing is not part of this file.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [DecidableEq G]





















theorem p2m_local_recoh_all_coefficient_formats_iff {I : Type*} [Fintype I]
    (p k : I → ℕ) (terms : I → RecohSparseTerms) :
    recohAllCoefficientFormats p k terms = true ↔
      ∀ i, RecohCoefficientFormat (p i) (k i) (terms i) := by
  simp [recohAllCoefficientFormats, recoh_coefficient_format_check_iff]

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {I : Type p2m_u_0} [inst : Fintype.{p2m_u_0} I] (p k : I → Nat) (terms : I → Couret.STROBO2TORS.RecohSparseTerms),
  Iff (@Eq.{1} Bool (@Couret.STROBO2TORS.recohAllCoefficientFormats.{p2m_u_0} I inst p k terms) Bool.true)
    (∀ (i : I), Couret.STROBO2TORS.RecohCoefficientFormat (p i) (k i) (terms i)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_all_coefficient_formats_iff

