-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_trace_eq_before_third
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:27:19.723422+00:00
-- url     : https://prove2.me/submissions/6413152f-a208-4a98-8454-cc3165061af8

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_even_trace_eq_of_square
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_no_early_quotient_return
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_ne_iff
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 — separation before the canonical third-period (18 October 2026).

RESEARCH PROOF CANDIDATES — NOT YET COMPILED.

This module separates two logically different tasks:
(1) if the image of a has order 3*ell and 3*delta=0, then no positive
    j<ell can reach +delta or -delta; this needs no cyclic classification;
(2) the quotient application transfers this fact into equality of the
    directed adjacency-matrix traces at EVERY degree strictly below ell.

It does NOT prove that ell*a is +delta or -delta: the canonical RETURN
theorem is still a distinct open Lean obligation. It also does NOT prove
the universal Newton identity needed for characteristic coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyFirstReturn



end Couret.CayleyFirstReturn

namespace Couret.CayleyDoublet

open Couret.CayleyFirstReturn

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





/-- Every *earlier* power trace coincides, not only the even traces,
provided that alpha has order 3*ell. The proof reuses the certified
odd-trace iff and square identity and handles even/odd exponents
separately. No appeal to the unproved Newton recurrence occurs here. -/
theorem p2m_local_abelianThree_trace_eq_before_third (a d h : G) (ell j : ℕ)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hord : addOrderOf (a : G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hjlt : j < ell) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ j) =
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ j) := by
  rcases Nat.even_or_odd j with ⟨n, hn⟩ | ⟨n, hn⟩
  · simpa [hn, two_mul] using
      abelianThree_even_trace_eq_of_square a d h hhalf hne hdorder n
  · have hjpos : 0 < j := by omega
    have hnot := abelianThree_no_early_quotient_return
      a d h ell j hord hdorder hjpos hjlt
    rw [hn] at hnot ⊢
    by_contra hdiff
    exact hnot ((abelianThree_odd_trace_ne_iff a d h
      hhalf hne hdorder n).mp hdiff)

end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d h : G) (ell j : Nat),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{1} Nat
          (@addOrderOf.{p2m_u_0}
            (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
            (@SubNegMonoid.toAddMonoid.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
              (@AddGroup.toSubNegMonoid.{p2m_u_0}
                (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                (@QuotientAddGroup.Quotient.addGroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                  (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
            (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @Eq.{1} Nat
            (@addOrderOf.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
              (@SubNegMonoid.toAddMonoid.{p2m_u_0}
                (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                (@AddGroup.toSubNegMonoid.{p2m_u_0}
                  (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                  (@QuotientAddGroup.Quotient.addGroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                    (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                      (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                      (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
              (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) a))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
          @LT.lt.{0} Nat instLTNat j ell →
            @Eq.{1} Rat
              (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                  (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                  (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                    (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                      (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                  j))
              (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                  (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                  (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                    (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                      (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                  j)) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_trace_eq_before_third

