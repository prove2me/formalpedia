-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationCollision_param_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:45.354819+00:00
-- url     : https://prove2.me/submissions/1aa05035-fefd-4535-8785-0789d272f6f0

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
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
import Theorems.Thm_Couret_STROBO2TORS_mem_paired_squareFibre
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_double_eq_neg
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Reflection in the unique singleton, in the canonical 3-torsion parameters. -/
theorem paramSupport_reflection (a d v : G) (hv : (v + v) + v = 0) :
    ({a, (a + v) + (a + v) - a, ((a + v) + (a + v) - a) + d} : Finset G) =
      paramSupport ((a, d), -v) := by
  have he : (a + v) + (a + v) - a = a + -v := by
    calc
      _ = a + (v + v) := by abel
      _ = _ := by rw [three_torsion_double_eq_neg v hv]
  simp only [he, paramSupport]

theorem paramSupport_exceptional (a d v u : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) (hu : u + u = 0) :
    ExceptionalPartner (paramSupport ((a, d), v))
      (translateSupport (paramSupport ((a, d), -v)) u) := by
  refine ⟨a, a + v, d, u, hd, hd0, exceptional_param_genuine a v hv hv0,
    hu, Or.inl (by simpa using hv), rfl, ?_⟩
  rw [paramSupport_reflection a d v hv]



section Finite
variable [Fintype G]

/-- Each exceptional ordered collision has a unique canonical source and
an H-translate of its reflection. No orbit-survival assumption is made. -/
theorem p2m_local_nontranslationCollision_param_iff (S T : Finset G) :
    NontranslationCollision S T ↔
      ∃ a d v u : G, d + d = 0 ∧ d ≠ 0 ∧ (v + v) + v = 0 ∧ v ≠ 0 ∧
        u + u = 0 ∧ S = paramSupport ((a, d), v) ∧
        T = translateSupport (paramSupport ((a, d), -v)) u ∧ 0 ∉ S ∧ 0 ∉ T := by
  constructor
  · rintro ⟨hS, hT, hzS, hzT, hsq, hn⟩
    have he : ExceptionalPartner S T := by
      rcases (orderedSquare_classification_iff S T hS hT).mp hsq with ho | he
      · exact (hn ⟨ho.choose, ho.choose_spec.2⟩).elim
      · exact he
    have hES := (mem_exceptionalSupports S).mpr ⟨hS, T, he⟩
    rw [exceptionalSupports_eq_params_image] at hES
    obtain ⟨⟨⟨a,d⟩,v⟩, hp, hs⟩ := Finset.mem_image.mp hES
    obtain ⟨hd, hd0, hv, hv0⟩ := (mem_exceptionalParams a d v).mp hp
    have hf : T ∈ squareFibre (paramSupport ((a,d),v)) :=
      (mem_squareFibre _ _).mpr ⟨hT, by simpa [hs] using hsq⟩
    have hf' := (mem_paired_squareFibre a (a+v) d hd hd0
      (exceptional_param_genuine a v hv hv0) T).mp hf
    rcases hf' with ho | ⟨_, hr⟩
    · obtain ⟨u, _, hu⟩ := (mem_torsionOrbit _ _).mp ho
      exact (hn ⟨u, by change T = translateSupport (paramSupport ((a,d),v)) u at hu; rwa [hs] at hu⟩).elim
    · rw [paramSupport_reflection a d v hv] at hr
      obtain ⟨u, hu, ht⟩ := (mem_torsionOrbit _ _).mp hr
      exact ⟨a,d,v,u,hd,hd0,hv,hv0,hu,hs.symm,ht,hzS,hzT⟩
  · rintro ⟨a,d,v,u,hd,hd0,hv,hv0,hu,rfl,rfl,hzS,hzT⟩
    have hS := paramSupport_card a d v hd hd0 hv hv0
    have hT : (translateSupport (paramSupport ((a,d),-v)) u).card = 3 := by
      rw [translateSupport_card]
      exact paramSupport_card a d (-v) hd hd0 (three_torsion_neg v hv) (neg_ne_zero.mpr hv0)
    have he := paramSupport_exceptional a d v u hd hd0 hv hv0 hu
    exact ⟨hS,hT,hzS,hzT, orderedSquare_eq_of_exceptionalPartner _ _ hT he,
      exceptionalPartner_not_any_translation _ _ hS hT he⟩






























attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (S T : Finset.{p2m_u_0} G),
  Iff (@Couret.STROBO2TORS.NontranslationCollision.{p2m_u_0} G inst inst_1 S T)
    (@Exists.{p2m_u_0 + 1} G fun a =>
      @Exists.{p2m_u_0 + 1} G fun d =>
        @Exists.{p2m_u_0 + 1} G fun v =>
          @Exists.{p2m_u_0 + 1} G fun u =>
            And
              (@Eq.{p2m_u_0 + 1} G
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  d d)
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
              (And
                (@Ne.{p2m_u_0 + 1} G d
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (And
                  (@Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        v v)
                      v)
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (And
                    (@Ne.{p2m_u_0 + 1} G v
                      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                        (@Zero.toOfNat0.{p2m_u_0} G
                          (@NegZeroClass.toZero.{p2m_u_0} G
                            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                    (And
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
                        (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S
                          (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                            (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                              (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v)))
                        (And
                          (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) T
                            (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
                              (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                                (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                                  (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d)
                                  (@Neg.neg.{p2m_u_0} G
                                    (@NegZeroClass.toNeg.{p2m_u_0} G
                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                    v)))
                              u))
                          (And
                            (Not
                              (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                                  (@Finset.instSetLike.{p2m_u_0} G))
                                S
                                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                  (@Zero.toOfNat0.{p2m_u_0} G
                                    (@NegZeroClass.toZero.{p2m_u_0} G
                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
                            (Not
                              (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                                  (@Finset.instSetLike.{p2m_u_0} G))
                                T
                                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                  (@Zero.toOfNat0.{p2m_u_0} G
                                    (@NegZeroClass.toZero.{p2m_u_0} G
                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationCollision_param_iff

