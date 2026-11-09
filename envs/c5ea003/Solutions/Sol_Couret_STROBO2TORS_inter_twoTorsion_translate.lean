-- Prove2me | solution 1 for Couret.STROBO2TORS.inter_twoTorsion_translate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:52.408242+00:00
-- url     : https://prove2.me/submissions/5a1fce54-cd63-4699-a603-7bf4b24ddc35

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

/-- An element is in G[2] exactly when its translate by a 2-torsion
element is in G[2]. -/
theorem twoTorsion_mem_translate_iff (x u : G) (hu : u + u = 0) :
    x + u ∈ (twoTorsion : Finset G) ↔ x ∈ (twoTorsion : Finset G) := by
  rw [mem_twoTorsion, mem_twoTorsion]
  have heq : (x + u) + (x + u) = (x + x) + (u + u) := by abel
  rw [heq, hu, add_zero]

/-- Intersecting a support with G[2] commutes with translating by G[2]. -/
theorem p2m_local_inter_twoTorsion_translate (S : Finset G) (u : G) (hu : u + u = 0) :
    translateSupport S u ∩ twoTorsion =
      translateSupport (S ∩ twoTorsion) u := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzS, hzH⟩ := Finset.mem_inter.mp hz
    change z ∈ S.image (fun x => x + u) at hzS
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hzS
    have hxHu : x + u ∈ (twoTorsion : Finset G) := by
      simpa [hxz] using hzH
    have hxH := (twoTorsion_mem_translate_iff x u hu).mp hxHu
    change z ∈ (S ∩ twoTorsion).image (fun x => x + u)
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_inter.mpr ⟨hx, hxH⟩, hxz⟩
  · intro hz
    change z ∈ (S ∩ twoTorsion).image (fun x => x + u) at hz
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
    obtain ⟨hxS, hxH⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_inter.mpr
    constructor
    · change z ∈ S.image (fun x => x + u)
      exact Finset.mem_image.mpr ⟨x, hxS, hxz⟩
    · have hxHu := (twoTorsion_mem_translate_iff x u hu).mpr hxH
      simpa [hxz] using hxHu











end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G) (u : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        u u)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
      (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1)
        (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u)
        (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
        (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
          (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        u) := @_root_.Couret.STROBO2TORS.p2m_local_inter_twoTorsion_translate

