-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalParamsProfile_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:23.933203+00:00
-- url     : https://prove2.me/submissions/244719b1-fc33-4187-9c86-5cbfd0124e0d

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

























/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/

/-- In the exceptional normal form, precisely the singleton lies in G[2]
if and only if the parameter a itself has order dividing two. -/
theorem paramSupport_profile_one_iff (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    (paramSupport ((a, d), v) ∩ (twoTorsion : Finset G)).card = 1 ↔
      a ∈ (twoTorsion : Finset G) := by
  rw [paramSupport_inter_twoTorsion_card a d v hd hd0 hv hv0, mem_twoTorsion]
  by_cases ha : a + a = 0
  · simp [ha]
  · by_cases hb : (a + v) + (a + v) = 0
    · simp [ha, hb]
    · simp [ha, hb]





/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/

/-- The profile-one exceptional parameters are exactly the direct product
of a in H, d in H\{0}, and v in G[3]\{0}. -/
theorem p2m_local_exceptionalParamsProfile_one_eq :
    (exceptionalParamsProfile (G := G) 1) =
      (((twoTorsion : Finset G).product ((twoTorsion : Finset G).erase 0)).product
        ((threeTorsion : Finset G).erase 0)) := by
  ext p
  rcases p with ⟨⟨a, d⟩, v⟩
  constructor
  · intro hp
    obtain ⟨hParams, hOne⟩ := Finset.mem_filter.mp hp
    obtain ⟨hd, hd0, hv, hv0⟩ := (mem_exceptionalParams a d v).mp hParams
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨(paramSupport_profile_one_iff a d v hd hd0 hv hv0).mp hOne,
        Finset.mem_erase.mpr ⟨hd0, (mem_twoTorsion d).mpr hd⟩⟩
    · exact Finset.mem_erase.mpr ⟨hv0, (mem_threeTorsion v).mpr hv⟩
  · intro hp
    obtain ⟨hpAD, hvMem⟩ := Finset.mem_product.mp hp
    obtain ⟨ha, hdMem⟩ := Finset.mem_product.mp hpAD
    obtain ⟨hd0, hd⟩ := Finset.mem_erase.mp hdMem
    obtain ⟨hv0, hv⟩ := Finset.mem_erase.mp hvMem
    have hD : d + d = 0 := (mem_twoTorsion d).mp hd
    have hV : (v + v) + v = 0 := (mem_threeTorsion v).mp hv
    exact Finset.mem_filter.mpr
      ⟨(mem_exceptionalParams a d v).mpr ⟨hD, hd0, hV, hv0⟩,
        (paramSupport_profile_one_iff a d v hD hd0 hV hv0).mpr ha⟩




/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G))
    (@Couret.STROBO2TORS.exceptionalParamsProfile.{p2m_u_0} G inst inst_1 inst_2
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@Finset.product.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
      (@Finset.product.{p2m_u_0, p2m_u_0} G G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)
        (@Finset.erase.{p2m_u_0} G inst_1 (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
      (@Finset.erase.{p2m_u_0} G inst_1 (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalParamsProfile_one_eq

