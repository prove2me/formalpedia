-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationPairs_preimage
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:47.836309+00:00
-- url     : https://prove2.me/submissions/d7fd678a-42dc-46b7-87e1-fd2279f6e6a8

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_NontranslationCollision_ne
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]
































attribute [local instance] Classical.propDecidable













omit [Fintype G] in
theorem NontranslationCollision.symm {S T : Finset G} (h : NontranslationCollision S T) :
    NontranslationCollision T S := by
  refine ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,fun z => (h.2.2.2.2.1 z).symm,?_⟩
  rintro ⟨u,hu⟩
  apply h.2.2.2.2.2
  refine ⟨-u,?_⟩
  rw [hu,translateSupport_add]
  simp [translateSupport]

/-- Exactly the two orientations lie above each unordered pair. -/
theorem p2m_local_nontranslationPairs_preimage (P : Finset (Finset G)) (hP : P ∈ nontranslationPairs) :
    ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
      (fun p => ({p.1,p.2} : Finset (Finset G))=P)).card = 2 := by
  obtain ⟨⟨S,T⟩,hp,rfl⟩ := Finset.mem_image.mp hP
  have hc := (mem_orderedNontranslationPairs S T).mp hp
  have he : ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
      (fun p => ({p.1,p.2} : Finset (Finset G))={S,T})) = {(S,T),(T,S)} := by
    ext p
    rcases p with ⟨A,B⟩
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
    constructor
    · rintro ⟨hab,hpair⟩
      have hA : A=S ∨ A=T := by have := congrArg (fun X : Finset (Finset G) => A ∈ X) hpair; simpa using this.mp (by simp)
      have hB : B=S ∨ B=T := by have := congrArg (fun X : Finset (Finset G) => B ∈ X) hpair; simpa using this.mp (by simp)
      have hne := ((mem_orderedNontranslationPairs A B).mp hab).ne
      rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> simp_all
    · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
      · subst A; subst B; exact ⟨hp,rfl⟩
      · subst A; subst B
        exact ⟨(mem_orderedNontranslationPairs T S).mpr hc.symm,Finset.pair_comm _ _⟩
  rw [he]
  simp [hc.ne]













end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (P : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.nontranslationPairs.{p2m_u_0} G inst inst_1 inst_2) P →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
          (fun p =>
            @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Insert.insert.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@Finset.instInsert.{p2m_u_0} (Finset.{p2m_u_0} G) fun a b =>
                  @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
                (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)
                (@Singleton.singleton.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                  (@Finset.instSingleton.{p2m_u_0} (Finset.{p2m_u_0} G))
                  (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)))
              P)
          (fun a =>
            @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
              (@Insert.insert.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@Finset.instInsert.{p2m_u_0} (Finset.{p2m_u_0} G) fun a b =>
                  @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
                (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)
                (@Singleton.singleton.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                  (@Finset.instSingleton.{p2m_u_0} (Finset.{p2m_u_0} G))
                  (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)))
              P)
          (@Couret.STROBO2TORS.orderedNontranslationPairs.{p2m_u_0} G inst inst_1 inst_2)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationPairs_preimage

