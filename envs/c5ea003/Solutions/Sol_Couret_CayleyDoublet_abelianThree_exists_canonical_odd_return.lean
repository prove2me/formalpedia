-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_exists_canonical_odd_return
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:11:39.096192+00:00
-- url     : https://prove2.me/submissions/cc45eb38-1473-435e-b2d9-a9ae76b76990

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_quotient_return
import Theorems.Thm_Couret_CayleyDoublet_odd_ell_of_odd_three_mul
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20, research-only quotient factor / first-coefficient assembly.
UNCOMPILED candidate (Lean 4.29.1). The first bridge eliminates explicit
arithmetic parameters ell, hell and hsize. The second derives a
noncospectrality theorem under finite-dimensional Newton recurrences.
-/
set_option autoImplicit false
noncomputable section

namespace Couret.CayleyThirdFactor

/-- Lagrange + parity: exact order three forces an odd finite group to
have cardinality 3*ell, with ell a positive odd natural number. -/
theorem odd_third_factor
    {Q : Type*} [AddGroup Q] [Finite Q]
    (delta : Q) (hdelta : addOrderOf delta = 3)
    (hodd : Odd (Nat.card Q)) :
    ∃ ell : ℕ, 0 < ell ∧ Odd ell ∧ Nat.card Q = 3 * ell := by
  have hdiv : 3 ∣ Nat.card Q := by
    rw [← hdelta]
    exact addOrderOf_dvd_natCard delta
  obtain ⟨ell, hcard⟩ := hdiv
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hell : 0 < ell := by omega
  have hoddell : Odd ell := by
    rw [hcard] at hodd
    exact Couret.CayleyDoublet.odd_ell_of_odd_three_mul ell hodd
  exact ⟨ell, hell, hoddell, hcard⟩

end Couret.CayleyThirdFactor

namespace Couret.CayleyDoublet

open Couret.CayleyThirdFactor
open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Canonical odd exponent exists, rather than being supplied as an
extra input. The quotient cardinal and exact order of d determine ell. -/
theorem p2m_local_abelianThree_exists_canonical_odd_return
    (a d h : G)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    ∃ ell : ℕ, 0 < ell ∧ Odd ell ∧
      Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * ell ∧
      (ell • a + d ∈ AddSubgroup.zmultiples h ∨
       ell • a - d ∈ AddSubgroup.zmultiples h) := by
  obtain ⟨ell, hell, hellodd, hsize⟩ :=
    odd_third_factor (d : G ⧸ AddSubgroup.zmultiples h) hdorder hodd
  exact ⟨ell, hell, hellodd, hsize,
    abelianThree_canonical_odd_quotient_return
      a d h ell hpair hodd hell hsize hdorder⟩



end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G] (a d h : G),
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
        @Exists.{1} Nat fun ell =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ell)
            (And (@Odd.{0} Nat Nat.instSemiring ell)
              (And
                (@Eq.{1} Nat
                  (Nat.card.{p2m_u_0}
                    (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell))
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
                      d))))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_exists_canonical_odd_return

