-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeOrdinaryFibres_card_le_twoTorsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:23.847686+00:00
-- url     : https://prove2.me/submissions/f7b9268b-0532-4f3f-b241-ed0eb4abdc6e

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

/-- An observed ordinary zero-free fibre cannot be larger than its
complete (labelled) square-convolution fibre of size |G[2]|. -/
theorem p2m_local_zeroFreeOrdinaryFibres_card_le_twoTorsion
    (R : Finset (Finset G))
    (hR : R ∈ (zeroFreeOrdinaryFibres : Finset (Finset (Finset G)))) :
    R.card ≤ (twoTorsion : Finset G).card := by
  obtain ⟨F, hF, hFR⟩ := Finset.mem_image.mp hR
  have hOrd : F ∈ (ordinaryFibres : Finset (Finset (Finset G))) :=
    (Finset.mem_filter.mp hF).1
  have hcard : F.card = (twoTorsion : Finset G).card :=
    (Finset.mem_filter.mp hOrd).2
  have hsubset : withoutZero F ⊆ F := by
    intro S hS
    exact (Finset.mem_filter.mp hS).1
  have hle := Finset.card_le_card hsubset
  rw [hFR, hcard] at hle
  exact hle







end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (R : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.zeroFreeOrdinaryFibres.{p2m_u_0} G inst inst_1 inst_2) R →
    @LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) R)
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeOrdinaryFibres_card_le_twoTorsion

