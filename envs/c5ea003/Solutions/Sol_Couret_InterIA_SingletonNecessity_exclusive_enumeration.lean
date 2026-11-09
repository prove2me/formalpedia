-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.exclusive_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:14.418823+00:00
-- url     : https://prove2.me/submissions/24ab5fc5-1ef7-4a22-b8c4-7fcdbbd62bb3

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_distinctLabels_of_injective_nonzero
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem p2m_local_exclusive_enumeration (A B : Finset G) (ha : A.card=4) (hb : B.card=4)
    (hi : A ∩ B={0}) :
    ∃ x : Fin 6 → G, SevenDistinct x ∧ supportLeft x=A ∧ supportRight x=B := by
  have hz : (0:G)∈A ∩ B := by rw [hi]; simp
  have ha0 := (Finset.mem_inter.mp hz).1
  have hb0 := (Finset.mem_inter.mp hz).2
  have hca : (A.erase 0).card=3 := by rw [Finset.card_erase_of_mem ha0,ha]
  have hcb : (B.erase 0).card=3 := by rw [Finset.card_erase_of_mem hb0,hb]
  obtain ⟨a,b,c,hab,hac,hbc,hAe⟩ := Finset.card_eq_three.mp hca
  obtain ⟨d,e,f,hde,hdf,hef,hBe⟩ := Finset.card_eq_three.mp hcb
  have an : a≠0 := (Finset.mem_erase.mp (show a∈A.erase 0 by rw [hAe]; simp)).1
  have bn : b≠0 := (Finset.mem_erase.mp (show b∈A.erase 0 by rw [hAe]; simp)).1
  have cn : c≠0 := (Finset.mem_erase.mp (show c∈A.erase 0 by rw [hAe]; simp)).1
  have dn : d≠0 := (Finset.mem_erase.mp (show d∈B.erase 0 by rw [hBe]; simp)).1
  have en : e≠0 := (Finset.mem_erase.mp (show e∈B.erase 0 by rw [hBe]; simp)).1
  have fn : f≠0 := (Finset.mem_erase.mp (show f∈B.erase 0 by rw [hBe]; simp)).1
  have cross (u v : G) (hu : u∈A.erase 0) (hv : v∈B.erase 0) : u≠v := by
    intro he
    subst v
    have hm : u∈A ∩ B := Finset.mem_inter.mpr
      ⟨(Finset.mem_erase.mp hu).2,(Finset.mem_erase.mp hv).2⟩
    have hu0 : u=0 := by simpa only [hi,Finset.mem_singleton] using hm
    exact (Finset.mem_erase.mp hu).1 hu0
  have had := cross a d (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hae := cross a e (by rw [hAe]; simp) (by rw [hBe]; simp)
  have haf := cross a f (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hbd := cross b d (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hbe := cross b e (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hbf := cross b f (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hcd := cross c d (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hce := cross c e (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hcf := cross c f (by rw [hAe]; simp) (by rw [hBe]; simp)
  have hA : A={0,a,b,c} := by
    calc A=insert 0 (A.erase 0) := (Finset.insert_erase ha0).symm
         _={0,a,b,c} := by rw [hAe]
  have hB : B={0,d,e,f} := by
    calc B=insert 0 (B.erase 0) := (Finset.insert_erase hb0).symm
         _={0,d,e,f} := by rw [hBe]
  let x : Fin 6 → G := fun i => ([a,b,c,d,e,f] : List G).get ⟨i.val,by simpa using i.isLt⟩
  have hx : Function.Injective x := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [x,hab,hac,hbc,hde,hdf,hef,had,hae,haf,hbd,hbe,hbf,hcd,hce,hcf,Ne.symm hab,Ne.symm hac,Ne.symm hbc,Ne.symm hde,Ne.symm hdf,Ne.symm hef,Ne.symm had,Ne.symm hae,Ne.symm haf,Ne.symm hbd,Ne.symm hbe,Ne.symm hbf,Ne.symm hcd,Ne.symm hce,Ne.symm hcf] at h ⊢
  have hn : ∀ i, x i≠0 := by
    intro i
    fin_cases i <;> simp [x,an,bn,cn,dn,en,fn]
  refine ⟨x,distinctLabels_of_injective_nonzero x hx hn,?_,?_⟩
  · change ({0,a,b,c}:Finset G)=A
    exact hA.symm
  · change ({0,d,e,f}:Finset G)=B
    exact hB.symm

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (A B : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G A) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G B) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
          (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) A B)
          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) →
        @Exists.{p2m_u_0 + 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G) fun x =>
          And (@Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x)
            (And
              (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                (@Couret.InterIA.SingletonNecessity.supportLeft.{p2m_u_0} G inst inst_1 x) A)
              (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                (@Couret.InterIA.SingletonNecessity.supportRight.{p2m_u_0} G inst inst_1 x) B)) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_exclusive_enumeration

