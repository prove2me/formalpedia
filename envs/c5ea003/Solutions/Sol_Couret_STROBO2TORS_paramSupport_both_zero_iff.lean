-- Prove2me | solution 1 for Couret.STROBO2TORS.paramSupport_both_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:46.158077+00:00
-- url     : https://prove2.me/submissions/e98cdfe5-e176-4528-8600-a574b3d26076

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
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_double_eq_neg
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]



omit [Fintype G] in
/-- Translation commutes with the canonical singleton parameter. -/
theorem translate_paramSupport (a d v u : G) :
    translateSupport (paramSupport ((a,d),v)) u = paramSupport ((a+u,d),v) := by
  simp only [paramSupport, translateSupport_three]
  congr 2 <;> abel_nf

/-- Zero occurs in both reflected supports only at their common singleton.
This is the one overlap in the six forbidden singleton parameters. -/
theorem p2m_local_paramSupport_both_zero_iff (a d v u : G)
    (hd : d+d=0) (hv : (v+v)+v=0) (hv0 : v ≠ 0) (hu : u+u=0) :
    (0 ∈ paramSupport ((a,d),v) ∧
      0 ∈ translateSupport (paramSupport ((a,d),-v)) u) ↔ a=0 ∧ u=0 := by
  have hab := exceptional_param_genuine a v hv hv0
  have hac := exceptional_param_genuine a (-v) (three_torsion_neg v hv) (neg_ne_zero.mpr hv0)
  have hbc : (a+v)+(a+v) ≠ (a + -v)+(a + -v) := by
    have h := exceptional_param_genuine (a+v) v hv hv0
    have he : (a+v)+v = a + -v := by rw [add_assoc, three_torsion_double_eq_neg v hv]
    rwa [he] at h
  have hleft : 0 ∈ paramSupport ((a,d),v) → a=0 ∨ (a+v)+(a+v)=0 := by
    simp only [paramSupport, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [← h]; simp)
    · right
      have he := pair_sum_translate (a+v) (a+v) d hd
      rw [← h] at he
      simpa using he.symm
  have hright : 0 ∈ translateSupport (paramSupport ((a,d),-v)) u →
      a+u=0 ∨ (a + -v)+(a + -v)=0 := by
    rw [translate_paramSupport]
    simp only [paramSupport, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact Or.inl h.symm
    · right
      have he := pair_sum_translate (a + -v) (a + -v) u hu
      have he' : (a+u)+ -v = (a + -v)+u := by abel
      rw [he'] at h
      rw [← h] at he
      simpa using he.symm
    · right
      have he := pair_sum_translate ((a + -v)+u) ((a + -v)+u) d hd
      have he' : (a+u)+ -v = (a + -v)+u := by abel
      rw [he'] at h
      rw [← h] at he
      have he2 := pair_sum_translate (a + -v) (a + -v) u hu
      simpa using he2.symm.trans he.symm
  constructor
  · rintro ⟨hl,hr⟩
    rcases hleft hl with ha | hb <;> rcases hright hr with hau | hc
    · exact ⟨ha, by simpa [ha] using hau⟩
    · exact (hac (by simpa [ha] using hc.symm)).elim
    · have ha : a+a=0 := by
        have he := pair_sum_translate a a u hu
        rw [hau] at he
        simpa using he.symm
      exact (hab (ha.trans hb.symm)).elim
    · exact (hbc (hb.trans hc.symm)).elim
  · rintro ⟨rfl,rfl⟩
    constructor <;> simp [paramSupport, translateSupport]


























attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (a d v u : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        d d)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            v v)
          v)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G v
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
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
          Iff
            (And
              (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
                (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                  (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v))
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
              (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
                (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
                  (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                    (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d)
                      (@Neg.neg.{p2m_u_0} G
                        (@NegZeroClass.toNeg.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                        v)))
                  u)
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
            (And
              (@Eq.{p2m_u_0 + 1} G a
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
              (@Eq.{p2m_u_0 + 1} G u
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_paramSupport_both_zero_iff

