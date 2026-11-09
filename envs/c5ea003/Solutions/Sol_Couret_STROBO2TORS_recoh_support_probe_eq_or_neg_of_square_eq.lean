-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_support_probe_eq_or_neg_of_square_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:01.462494+00:00
-- url     : https://prove2.me/submissions/f7a6869d-e864-4831-9250-3b4198ad979d

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_sq
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

/-!
The actual ordered convolution square determines the square of every
individual labelled complex character coefficient.  This is a finite-sum
identity for arbitrary supports, independent of the triple classification.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



/-- Equality of labelled ordered squares fixes the square of every probe.
No nonvanishing or cardinality assumption is required. -/
theorem recoh_support_probe_sq_eq_of_square_eq
    (chi : AddChar G ℂ) (S T : Finset G)
    (hsquare : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    (recohSupportProbe chi S) ^ 2 = (recohSupportProbe chi T) ^ 2 := by
  rw [recoh_support_probe_sq, recoh_support_probe_sq]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hsquare z]

/-- A probe takes at most the two opposite values on a square fibre.  The
two alternatives may coincide at zero; no choice of a square root is used. -/
theorem p2m_local_recoh_support_probe_eq_or_neg_of_square_eq
    (chi : AddChar G ℂ) (S T : Finset G)
    (hsquare : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    recohSupportProbe chi S = recohSupportProbe chi T ∨
      recohSupportProbe chi S = -recohSupportProbe chi T := by
  have hsq := recoh_support_probe_sq_eq_of_square_eq chi S T hsquare
  have hfactor :
      (recohSupportProbe chi S - recohSupportProbe chi T) *
        (recohSupportProbe chi S + recohSupportProbe chi T) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (chi :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S T : Finset.{p2m_u_0} G),
  (∀ (z : G),
      @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
        (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z)) →
    Or
      (@Eq.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi S)
        (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi T))
      (@Eq.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi S)
        (@Neg.neg.{0} Complex Complex.instNeg (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi T))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_support_probe_eq_or_neg_of_square_eq

