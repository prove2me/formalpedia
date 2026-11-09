-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_canonical_odd_quotient_return
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:34.979492+00:00
-- url     : https://prove2.me/submissions/f0847830-626d-4636-bcd3-e6e4afe08743

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyCanonical_canonical_of_odd_cyclic
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_zmultiples_generator_of_pair
import Theorems.Thm_Couret_CayleyDoublet_quotient_alpha_order_of_pair_generation
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

/-- Canonical witness modulo H; keeps the original group hypotheses and
the quotient's exact size 3*ell explicit. The independent arithmetic
obligations 3|card Q and odd ell can later discharge hcard and hell. -/
theorem p2m_local_abelianThree_canonical_odd_quotient_return
    (a d h : G) (ell : ℕ)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hell : 0 < ell)
    (hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    (ell • a + d ∈ AddSubgroup.zmultiples h ∨
     ell • a - d ∈ AddSubgroup.zmultiples h) := by
  classical
  let H : AddSubgroup G := AddSubgroup.zmultiples h
  have hgen : AddSubgroup.zmultiples (a : G ⧸ H) = ⊤ :=
    abelian_quotient_zmultiples_generator_of_pair a h hpair
  have hord : addOrderOf (a : G ⧸ H) = 3 * ell := by
    rw [quotient_alpha_order_of_pair_generation a h hpair, hsize]
  rcases canonical_of_odd_cyclic (a : G ⧸ H) (d : G ⧸ H) ell
      hgen hodd hell hord hdorder with hplus | hminus
  · right
    apply (QuotientAddGroup.eq_zero_iff (ell • a - d)).mp
    change ell • (a : G ⧸ H) - (d : G ⧸ H) = 0
    rw [hplus]
    exact sub_self _
  · left
    apply (QuotientAddGroup.eq_zero_iff (ell • a + d)).mp
    change ell • (a : G ⧸ H) + (d : G ⧸ H) = 0
    rw [hminus]
    exact neg_add_cancel _








end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G] (a d h : G)
  (ell : Nat),
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
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
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
                      (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                        (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                        (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
                (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            Or
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
                    ell a)
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
                    ell a)
                  d)) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_canonical_odd_quotient_return

