-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_support_probe_sq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:12.438237+00:00
-- url     : https://prove2.me/submissions/35cdec7b-0a55-4c3d-b920-650b91175077

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

/-- The Fourier transform of the labelled ordered square is the algebraic
square of the support coefficient, including diagonal contributions. -/
theorem p2m_local_recoh_support_probe_sq (chi : AddChar G ℂ) (S : Finset G) :
    (recohSupportProbe chi S) ^ 2 =
      ∑ z : G, (orderedSquare S z : ℂ) * chi z := by
  classical
  have hcast (z : G) :
      (orderedSquare S z : ℂ) =
        ∑ x ∈ S, ∑ y ∈ S, if x + y = z then (1 : ℂ) else 0 := by
    simp [orderedSquare]
  symm
  calc
    (∑ z : G, (orderedSquare S z : ℂ) * chi z) =
        ∑ z : G, ∑ x ∈ S, ∑ y ∈ S,
          (if x + y = z then (1 : ℂ) else 0) * chi z := by
      simp only [hcast, Finset.sum_mul]
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ z : G,
          (if x + y = z then (1 : ℂ) else 0) * chi z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ S, ∑ y ∈ S, chi (x + y) := by
      simp [ite_mul]
    _ = (recohSupportProbe chi S) ^ 2 := by
      simp [recohSupportProbe, chi.map_add_eq_mul, pow_two,
        Finset.sum_mul, Finset.mul_sum, mul_comm]





end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G]
  (chi :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S : Finset.{p2m_u_0} G),
  @Eq.{1} Complex
    (@HPow.hPow.{0, 0, 0} Complex Nat Complex
      (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
      (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi S)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Finset.sum.{p2m_u_0, 0} G Complex
      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
              (@CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing)))))
      (@Finset.univ.{p2m_u_0} G inst_2) fun z =>
      @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
        (@Nat.cast.{0} Complex Complex.instNatCast (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z))
        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
          (@AddChar.{p2m_u_0, 0} G
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          G (fun x => Complex)
          (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          chi z)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_support_probe_sq

