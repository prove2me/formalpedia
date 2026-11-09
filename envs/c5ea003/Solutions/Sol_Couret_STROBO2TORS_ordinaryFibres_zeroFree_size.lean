-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibres_zeroFree_size
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:00.468979+00:00
-- url     : https://prove2.me/submissions/e616fa40-412c-4858-9d34-0a671dc7e985

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_squareFibre
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareFibre_card_of_no_exception
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]













/-- An ordinary fibre has size h minus the number of its support vertices in G[2]
after removing the neutral element. -/
theorem p2m_local_ordinaryFibres_zeroFree_size (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G)))) :
    ∃ S : Finset G, S.card = 3 ∧ squareFibre S = F ∧
      (withoutZero F).card =
        (twoTorsion : Finset G).card - (S ∩ (twoTorsion : Finset G)).card := by
  obtain ⟨hAll, hcard⟩ := Finset.mem_filter.mp hF
  obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hAll
  have hS3 : S.card = 3 := (mem_tripleSupports S).mp hS
  have hne : ∀ T : Finset G, ¬ ExceptionalPartner S T := by
    intro T hEx
    have htwo := (squareFibre_card_two_h_iff_exception S hS3).mpr ⟨T, hEx⟩
    rw [hsF] at htwo
    have hp := twoTorsion_card_pos (G := G)
    omega
  have hsize := zeroFreeSquareFibre_card_of_no_exception S hS3 hne
  rw [← withoutZero_squareFibre, hsF] at hsize
  exact ⟨S, hS3, hsF, hsize⟩























/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2) F →
    @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
      And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (And
          (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) F)
          (@Eq.{1} Nat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@Finset.card.{p2m_u_0} G
                (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
                  (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibres_zeroFree_size

