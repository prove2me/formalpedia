-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_no_early_quotient_return
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:41.730387+00:00
-- url     : https://prove2.me/submissions/27bd5f27-c3ec-4a03-a250-53f1f97a5ba0

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyFirstReturn_no_early_three_torsion_return
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



/-- With quotient order 3*ell, no j in (0,ell) returns to ±d mod <h>.
No choice of a basis, isomorphism to ZMod, or test of graph loops is
needed: this is an additive-group argument. -/
theorem p2m_local_abelianThree_no_early_quotient_return (a d h : G) (ell j : ℕ)
    (hord : addOrderOf (a : G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hjpos : 0 < j) (hjlt : j < ell) :
    ¬ (j • a + d ∈ AddSubgroup.zmultiples h ∨
       j • a - d ∈ AddSubgroup.zmultiples h) := by
  classical
  let H : AddSubgroup G := AddSubgroup.zmultiples h
  have hthree : (3 : ℕ) • (d : G ⧸ H) = 0 := by
    have hd := addOrderOf_nsmul_eq_zero (d : G ⧸ H)
    rw [hdorder] at hd
    exact hd
  have hshort := no_early_three_torsion_return
    (a : G ⧸ H) (d : G ⧸ H) ell j hord hthree hjpos hjlt
  rintro (hp | hm)
  · have hz : (QuotientAddGroup.mk' H) (j • a + d) = 0 :=
      (QuotientAddGroup.eq_zero_iff (j • a + d)).mpr hp
    have hsum : j • (a : G ⧸ H) + (d : G ⧸ H) = 0 := by
      simpa only [map_add, map_nsmul, QuotientAddGroup.mk'_apply] using hz
    have heq : j • (a : G ⧸ H) = -(d : G ⧸ H) := by
      calc
        j • (a : G ⧸ H) =
            (j • (a : G ⧸ H) + (d : G ⧸ H)) - (d : G ⧸ H) := by abel
        _ = -(d : G ⧸ H) := by rw [hsum]; simp
    exact hshort.2 heq
  · have hz : (QuotientAddGroup.mk' H) (j • a - d) = 0 :=
      (QuotientAddGroup.eq_zero_iff (j • a - d)).mpr hm
    have hsub : j • (a : G ⧸ H) - (d : G ⧸ H) = 0 := by
      simpa only [map_sub, map_nsmul, QuotientAddGroup.mk'_apply] using hz
    exact hshort.1 (sub_eq_zero.mp hsub)



end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G] (a d h : G)
  (ell j : Nat),
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
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
        (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
          (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) a))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
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
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
          (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
            (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
        @LT.lt.{0} Nat instLTNat j ell →
          Not
            (Or
              (@Membership.mem.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                  (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
                    (@instHSMul.{0, p2m_u_0} Nat G
                      (@AddMonoid.toNSMul.{p2m_u_0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                    j a)
                  d))
              (@Membership.mem.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                  (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHSub.{p2m_u_0} G
                    (@SubNegMonoid.toSub.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                  (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
                    (@instHSMul.{0, p2m_u_0} Nat G
                      (@AddMonoid.toNSMul.{p2m_u_0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                    j a)
                  d))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_no_early_quotient_return

