-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeOrbit_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:17.271349+00:00
-- url     : https://prove2.me/submissions/e622d12d-d543-466a-885b-1aef0a8607fd

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective_on_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrbit_image
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]











































/-- Excluding zero removes exactly one translate for each support element in G[2]. -/
theorem p2m_local_zeroFreeOrbit_card (S : Finset G) (hS : S.card = 3) :
    (zeroFreeOrbit S).card = (twoTorsion : Finset G).card -
      (S ∩ (twoTorsion : Finset G)).card := by
  rw [zeroFreeOrbit_image]
  have hi : (((twoTorsion : Finset G).filter (fun u => u ∉ S)).image
      (fun u => translateSupport S u)).card =
        ((twoTorsion : Finset G).filter (fun u => u ∉ S)).card := by
    apply Finset.card_image_iff.mpr
    intro u hu v hv heq
    exact translateSupport_injective_on_two_torsion S hS u v
      ((mem_twoTorsion u).mp (Finset.mem_filter.mp hu).1)
      ((mem_twoTorsion v).mp (Finset.mem_filter.mp hv).1) heq
  rw [hi]
  have hf : (twoTorsion : Finset G).filter (fun u => u ∈ S) = S ∩ twoTorsion := by
    ext u; simp [and_comm]
  have hc := Finset.card_filter_add_card_filter_not (s := (twoTorsion : Finset G))
    (fun u => u ∈ S)
  rw [hf] at hc
  omega






/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.zeroFreeOrbit.{p2m_u_0} G inst inst_1 inst_2 S))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@Finset.card.{p2m_u_0} G
          (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
            (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeOrbit_card

