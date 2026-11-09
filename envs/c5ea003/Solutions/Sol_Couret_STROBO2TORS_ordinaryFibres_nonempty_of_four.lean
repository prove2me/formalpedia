-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibres_nonempty_of_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:17.285248+00:00
-- url     : https://prove2.me/submissions/a46aa638-e19f-41ad-b03d-1f90da7e2a2a

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]















/-- All ordinary fibres survive zero removal when the two-torsion subgroup
has at least four elements. Small h=1 and h=2 require deleting empty restrictions. -/
theorem p2m_local_ordinaryFibres_nonempty_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card)
    (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G)))) :
    (withoutZero F).Nonempty := by
  obtain ⟨S, hS3, _, hsize⟩ := ordinaryFibres_zeroFree_size F hF
  have hle : (S ∩ (twoTorsion : Finset G)).card ≤ 3 := by
    calc
      (S ∩ (twoTorsion : Finset G)).card ≤ S.card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hS3
  apply Finset.card_pos.mp
  omega





















/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
    ∀ (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
          (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2) F →
        @Finset.Nonempty.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibres_nonempty_of_four

