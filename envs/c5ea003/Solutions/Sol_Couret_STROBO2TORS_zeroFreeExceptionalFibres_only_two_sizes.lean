-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeExceptionalFibres_only_two_sizes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:46.042362+00:00
-- url     : https://prove2.me/submissions/cc6152a0-2dfd-4fb6-a8d8-97e34c8db874

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





























/-- Every exceptional zero-free fibre has one of the two certified sizes.
This is a statement about actual images, not a classification by size. -/
theorem p2m_local_zeroFreeExceptionalFibres_only_two_sizes (R : Finset (Finset G))
    (hR : R ∈ (zeroFreeExceptionalFibres : Finset (Finset (Finset G)))) :
    R.card = 2 * (twoTorsion : Finset G).card - 2 ∨
      R.card = 2 * (twoTorsion : Finset G).card := by
  obtain ⟨F, hF, hFR⟩ := Finset.mem_image.mp hR
  rcases exceptionalFibres_zeroFree_card F hF with hr | hf
  · left
    rw [← hFR]
    exact hr
  · right
    rw [← hFR]
    exact hf







/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (R : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.zeroFreeExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2) R →
    Or
      (@Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeExceptionalFibres_only_two_sizes

