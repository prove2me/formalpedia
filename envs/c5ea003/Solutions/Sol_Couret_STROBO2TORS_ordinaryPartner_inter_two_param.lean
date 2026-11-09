-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryPartner_inter_two_param
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:37.135829+00:00
-- url     : https://prove2.me/submissions/032f78a4-beb3-4164-a219-8ce450a61894

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_inter_translateSupport_add_mem
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact count of the ordinary delta-two edges, with zero allowed.

Parameters (a,u,b) have u a nonzero element of G[2] and b outside
{a,a+u}. They represent the ordered pair
({a,a+u,b}, {a,a+u,b+u}). Each ordered pair has precisely two
parameters, according to the choice a or a+u in its common pair.
The graph handshake supplies the second factor of two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private theorem deltaTwo_ne_add_self (a u : G) (hu0 : u ≠ 0) :
    a ≠ a + u := by
  intro h
  apply hu0
  exact (add_left_cancel (show a + 0 = a + u by simpa using h)).symm



private theorem deltaTwo_target_translate (a u b : G) (hu : u + u = 0) :
    ({a, a + u, b + u} : Finset G) =
      translateSupport ({a, a + u, b} : Finset G) u := by
  rw [translateSupport_three]
  have hshift : (a + u) + u = a := by simp [add_assoc, hu]
  rw [hshift]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto





/-- Every ordinary pair with two common points has the exact parameter form
used by the delta-two count. -/
theorem p2m_local_ordinaryPartner_inter_two_param
    (S T : Finset G) (hS : S.card = 3)
    (hOrd : OrdinaryPartner S T) (hI : (S ∩ T).card = 2) :
    ∃ a u b : G, u + u = 0 ∧ u ≠ 0 ∧ b ≠ a ∧ b ≠ a + u ∧
      S = {a, a + u, b} ∧ T = {a, a + u, b + u} := by
  obtain ⟨u, hu, hTu⟩ := hOrd
  have hu0 : u ≠ 0 := by
    intro hz
    have hTS : T = S := by simpa [hz, translateSupport] using hTu
    rw [hTS, Finset.inter_self, hS] at hI
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (S ∩ T).card by omega)
  have hau : a + u ∈ S ∩ T := by
    rw [hTu] at ha ⊢
    exact inter_translateSupport_add_mem S u hu a ha
  have hane := deltaTwo_ne_add_self a u hu0
  have hpairSub : ({a, a + u} : Finset G) ⊆ S ∩ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hau
  have hpairCard : ({a, a + u} : Finset G).card = 2 := by simp [hane]
  have hpair : S ∩ T = {a, a + u} :=
    (Finset.eq_of_subset_of_card_le hpairSub (by omega)).symm
  have hdiffCard : (S \ T).card = 1 := by
    have := Finset.card_sdiff_add_card_inter S T
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hdiffCard
  have hbmem : b ∈ S \ T := by rw [hb]; simp
  have hbS := (Finset.mem_sdiff.mp hbmem).1
  have hbT := (Finset.mem_sdiff.mp hbmem).2
  have hba : b ≠ a := by
    intro heq
    apply hbT
    rw [heq]
    exact (Finset.mem_inter.mp ha).2
  have hbau : b ≠ a + u := by
    intro heq
    apply hbT
    rw [heq]
    exact (Finset.mem_inter.mp hau).2
  have hs : S = {a, a + u, b} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxT : x ∈ T
      · have hxI : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨hx, hxT⟩
        rw [hpair] at hxI
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxI
        tauto
      · have hxD : x ∈ S \ T := Finset.mem_sdiff.mpr ⟨hx, hxT⟩
        rw [hb] at hxD
        exact Or.inr (Or.inr (Finset.mem_singleton.mp hxD))
    · rintro (rfl | rfl | rfl)
      · exact (Finset.mem_inter.mp ha).1
      · exact (Finset.mem_inter.mp hau).1
      · exact hbS
  refine ⟨a, u, b, hu, hu0, hba, hbau, hs, ?_⟩
  rw [hTu, hs]
  exact (deltaTwo_target_translate a u b hu).symm

variable [Fintype G]











attribute [local instance] Classical.propDecidable






















end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 S T →
      @Eq.{1} Nat
          (@Finset.card.{p2m_u_0} G
            (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S T))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Exists.{p2m_u_0 + 1} G fun a =>
          @Exists.{p2m_u_0 + 1} G fun u =>
            @Exists.{p2m_u_0 + 1} G fun b =>
              And
                (@Eq.{p2m_u_0 + 1} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    u u)
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (And
                  (@Ne.{p2m_u_0 + 1} G u
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (And (@Ne.{p2m_u_0 + 1} G b a)
                    (And
                      (@Ne.{p2m_u_0 + 1} G b
                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHAdd.{p2m_u_0} G
                            (@AddCommMagma.toAdd.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                          a u))
                      (And
                        (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S
                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instInsert.{p2m_u_0} G inst_1) a
                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                (@instHAdd.{p2m_u_0} G
                                  (@AddCommMagma.toAdd.{p2m_u_0} G
                                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                a u)
                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@Finset.instSingleton.{p2m_u_0} G) b))))
                        (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) T
                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instInsert.{p2m_u_0} G inst_1) a
                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                (@instHAdd.{p2m_u_0} G
                                  (@AddCommMagma.toAdd.{p2m_u_0} G
                                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                a u)
                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@Finset.instSingleton.{p2m_u_0} G)
                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                  (@instHAdd.{p2m_u_0} G
                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                  b u))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryPartner_inter_two_param

