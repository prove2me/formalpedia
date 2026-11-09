-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_charpoly_ne_of_newton_prefix
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:36:46.537265+00:00
-- url     : https://prove2.me/submissions/328eaedf-0633-46dd-b4a9-421eab6f1948

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_trace_difference
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_trace_eq_before_third
import Theorems.Thm_Couret_CayleyDoublet_quotient_alpha_order_of_pair_generation
import Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_ne_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_reverseCharpolyCoeff_congr
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 -- canonical order-three return in the odd cyclic quotient.
Research source, **UNCOMPILED** with pinned Lean 4.29.1.
No existing certified theorem has been modified.

The first lemma needs only the order of alpha and a bounded coordinate,
and is independent of any representation of a directed graph. The last
lemma translates its canonical witness back to the quotient G/<h>.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyCanonical







end Couret.CayleyCanonical

namespace Couret.CayleyDoublet

open Couret.CayleyCanonical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








/-- Conditional complete first-coefficient obstruction. Unlike the
earlier hbridge, the only remaining analytic input is a FINITE prefix
of ordinary single-matrix Newton equations at degrees <= ell.
The return at ell and all lower trace equalities are derived from the
group hypotheses. -/
theorem p2m_local_abelianThree_charpoly_ne_of_newton_prefix
    (a d h : G) (ell : ℕ)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hell : 0 < ell)
    (hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hS : ∀ k : ℕ, 0 < k → k ≤ ell →
      Couret.CayleyNewton.NewtonTraceEquation
        (Couret.CayleyNewton.reverseCharpolyCoeff
          (abelianCayleyMatrix (AbelianSource a d h)))
        (fun m => Matrix.trace
          (abelianCayleyMatrix (AbelianSource a d h) ^ m)) k)
    (hT : ∀ k : ℕ, 0 < k → k ≤ ell →
      Couret.CayleyNewton.NewtonTraceEquation
        (Couret.CayleyNewton.reverseCharpolyCoeff
          (abelianCayleyMatrix (AbelianTarget a d h)))
        (fun m => Matrix.trace
          (abelianCayleyMatrix (AbelianTarget a d h) ^ m)) k) :
    (abelianCayleyMatrix (AbelianSource a d h)).charpoly ≠
      (abelianCayleyMatrix (AbelianTarget a d h)).charpoly := by
  let A := abelianCayleyMatrix (AbelianSource a d h)
  let B := abelianCayleyMatrix (AbelianTarget a d h)
  have hord : addOrderOf (a : G ⧸ AddSubgroup.zmultiples h) =
      3 * ell := by
    rw [quotient_alpha_order_of_pair_generation a h hpair, hsize]
  have hprev : ∀ k : ℕ, 0 < k → k < ell →
      Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
    intro k _ hk
    exact abelianThree_trace_eq_before_third a d h ell k
      hhalf hne hdorder hord hk
  have hdiff : Matrix.trace (A ^ ell) ≠ Matrix.trace (B ^ ell) :=
    abelianThree_canonical_odd_trace_difference a d h ell
      hhalf hne hpair hodd hell hsize hdorder
  have hcoeff : Couret.CayleyNewton.reverseCharpolyCoeff A ell ≠
      Couret.CayleyNewton.reverseCharpolyCoeff B ell :=
    Couret.CayleyNewton.newton_first_coefficient_ne_of_trace_prefix
      (Couret.CayleyNewton.reverseCharpolyCoeff A)
      (Couret.CayleyNewton.reverseCharpolyCoeff B)
      (fun k => Matrix.trace (A ^ k))
      (fun k => Matrix.trace (B ^ k))
      ell hell hS hT hprev hdiff
  intro hp
  exact hcoeff (congrFun
    (Couret.CayleyNewton.reverseCharpolyCoeff_congr A B hp) ell)

end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d h : G) (ell : Nat),
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
      @Eq.{p2m_u_0 + 1} (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@AddSubgroup.closure.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Set.{p2m_u_0} G) (@Set.instInsert.{p2m_u_0} G) a
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Set.{p2m_u_0} G) (@Set.instSingletonSet.{p2m_u_0} G) h)))
          (@Top.top.{p2m_u_0} (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@AddSubgroup.instTop.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))) →
        @Odd.{0} Nat Nat.instSemiring
            (Nat.card.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))) →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ell →
            @Eq.{1} Nat
                (Nat.card.{p2m_u_0}
                  (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
              @Eq.{1} Nat
                  (@addOrderOf.{p2m_u_0}
                    (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0}
                      (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                      (@AddGroup.toSubNegMonoid.{p2m_u_0}
                        (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                          (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                            (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                          (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                        (@QuotientAddGroup.Quotient.addGroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                          (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                          (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G
                            (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                            (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                            (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
                    (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                      (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                (∀ (k : Nat),
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
                      @LE.le.{0} Nat instLENat k ell →
                        Couret.CayleyNewton.NewtonTraceEquation
                          (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                            (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                              (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h)))
                          (fun m =>
                            @Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                              (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                                (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                                  (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                    (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                      (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                                (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                                  (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                                m))
                          k) →
                  (∀ (k : Nat),
                      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
                        @LE.le.{0} Nat instLENat k ell →
                          Couret.CayleyNewton.NewtonTraceEquation
                            (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                              (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                                (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h)))
                            (fun m =>
                              @Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                                (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                                  (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                  (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                                    (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                      (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                        (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                                    (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                                  m))
                            k) →
                    @Ne.{1}
                      (@Polynomial.{0} Rat
                        (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
                      (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                        (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                          (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h)))
                      (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                        (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                          (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_charpoly_ne_of_newton_prefix

