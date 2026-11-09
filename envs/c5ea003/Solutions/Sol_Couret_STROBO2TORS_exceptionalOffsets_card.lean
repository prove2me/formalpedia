-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalOffsets_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:43.918063+00:00
-- url     : https://prove2.me/submissions/de00ee4d-eb73-4645-8501-7566c09880b5

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalOffsets_disjoint
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/





















/-- There are twice as many exceptional offsets as nonzero 3-torsion
elements, for each fixed nonzero direction d of order two. This is NOT
yet a formula for the number of exceptional square fibres. -/
theorem p2m_local_exceptionalOffsets_card (d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) :
    (exceptionalOffsets d).card =
      2 * (nonzeroThreeTorsion : Finset G).card := by
  unfold exceptionalOffsets
  rw [Finset.card_union_of_disjoint (exceptionalOffsets_disjoint d hd hd0)]
  have hi : ((nonzeroThreeTorsion : Finset G).image (fun w => w + d)).card =
      (nonzeroThreeTorsion : Finset G).card := by
    apply Finset.card_image_iff.mpr
    intro u hu v hv h
    exact add_right_cancel h
  rw [hi]
  omega

end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (d : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        d d)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G d
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.exceptionalOffsets.{p2m_u_0} G inst inst_1 inst_2 d))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.nonzeroThreeTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalOffsets_card

