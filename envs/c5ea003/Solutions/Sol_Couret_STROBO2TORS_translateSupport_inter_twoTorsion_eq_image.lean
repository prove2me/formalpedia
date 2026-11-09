-- Prove2me | solution 1 for Couret.STROBO2TORS.translateSupport_inter_twoTorsion_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:33.083209+00:00
-- url     : https://prove2.me/submissions/b9069ae6-94b0-4400-8f30-4f5bc02091ee

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





































/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/

/-- Membership in G[2] is unchanged by translation through G[2]. -/
theorem twoTorsion_add_mem_iff (x u : G)
    (hu : u ∈ (twoTorsion : Finset G)) :
    x + u ∈ (twoTorsion : Finset G) ↔ x ∈ (twoTorsion : Finset G) := by
  have hu' : u + u = 0 := (mem_twoTorsion u).mp hu
  have h : (x + u) + (x + u) = (x + x) + (u + u) := by abel
  rw [mem_twoTorsion, mem_twoTorsion, h, hu', add_zero]

/-- Translation of a support commutes with intersection with G[2]. -/
theorem p2m_local_translateSupport_inter_twoTorsion_eq_image (S : Finset G) (u : G)
    (hu : u ∈ (twoTorsion : Finset G)) :
    translateSupport S u ∩ (twoTorsion : Finset G) =
      (S ∩ (twoTorsion : Finset G)).image (fun x => x + u) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hxH⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxS
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_inter.mpr ⟨ha, (twoTorsion_add_mem_iff a u hu).mp hxH⟩, rfl⟩
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨haS, haH⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨a, haS, rfl⟩,
       (twoTorsion_add_mem_iff a u hu).mpr haH⟩











/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G) (u : G),
  @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
      (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2) u →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
      (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1)
        (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u)
        (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@Finset.image.{p2m_u_0, p2m_u_0} G G inst_1
        (fun x =>
          @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            x u)
        (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
          (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_translateSupport_inter_twoTorsion_eq_image

