-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalPartner_normalized_inter
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:57.333925+00:00
-- url     : https://prove2.me/submissions/f888f2b8-881d-48cc-b898-5456f620faa8

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Intersection sizes for the exceptional branch of the triple-square
classification. The parameters below use the same coordinates as
ExceptionalPartner: the reflected doublet is based at b + b - a.
No finiteness assumption on the ambient abelian group is needed.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private theorem deltaExceptional_pair_double_ne_reflected_double
    (a b : G) (hab : a + a ≠ b + b) :
    b + b ≠ (b + b - a) + (b + b - a) := by
  intro h
  apply hab
  apply sub_eq_zero.mp
  calc
    (a + a) - (b + b) =
        (b + b) - ((b + b - a) + (b + b - a)) := by abel
    _ = 0 := by rw [← h]; simp

private theorem deltaExceptional_singleton_double_ne_reflected_double
    (a b d : G) (hd : d + d = 0) (hab : a + a ≠ b + b)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d) :
    a + a ≠ (b + b - a) + (b + b - a) := by
  intro h
  have hee : (b + b - a) + (b + b - a) =
      (a + b) + (((b - a) + (b - a)) + (b - a)) := by abel
  rcases h3 with hzero | hdiff
  · have hbase : a + a = a + b := by
      calc
        a + a = (b + b - a) + (b + b - a) := h
        _ = a + b := by rw [hee, hzero]; simp
    have habase : a = b := add_left_cancel hbase
    exact hab (by rw [habase])
  · have hbase : a + a = a + (b + d) := by
      calc
        a + a = (b + b - a) + (b + b - a) := h
        _ = (a + b) + d := by rw [hee, hdiff]
        _ = a + (b + d) := by abel
    have habase : a = b + d := add_left_cancel hbase
    apply hab
    calc
      a + a = (b + d) + (b + d) := by rw [habase]
      _ = b + b := pair_sum_translate b b d hd

private theorem deltaExceptional_common_mem
    (a b d u z : G) (hd : d + d = 0) (hab : a + a ≠ b + b)
    (hu : u + u = 0)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d)
    (hzS : z ∈ ({a, b, b + d} : Finset G))
    (hzT : z ∈ translateSupport
      ({a, b + b - a, (b + b - a) + d} : Finset G) u) :
    z = a ∧ z = a + u := by
  let e : G := b + b - a
  have hae : a + a ≠ e + e :=
    deltaExceptional_singleton_double_ne_reflected_double a b d hd hab h3
  have hbe : b + b ≠ e + e :=
    deltaExceptional_pair_double_ne_reflected_double a b hab
  change z ∈ translateSupport ({a, e, e + d} : Finset G) u at hzT
  rw [translateSupport_three] at hzT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzS hzT
  have hs2 : z + z = a + a ∨ z + z = b + b := by
    rcases hzS with hz | hz | hz
    · exact Or.inl (congrArg (fun w : G => w + w) hz)
    · exact Or.inr (congrArg (fun w : G => w + w) hz)
    · exact Or.inr ((congrArg (fun w : G => w + w) hz).trans
        (pair_sum_translate b b d hd))
  have ht2 : z + z = a + a ∨ z + z = e + e := by
    rcases hzT with hz | hz | hz
    · exact Or.inl ((congrArg (fun w : G => w + w) hz).trans
        (pair_sum_translate a a u hu))
    · exact Or.inr ((congrArg (fun w : G => w + w) hz).trans
        (pair_sum_translate e e u hu))
    · exact Or.inr (((congrArg (fun w : G => w + w) hz).trans
        (pair_sum_translate (e + d) (e + d) u hu)).trans
        (pair_sum_translate e e d hd))
  have hzaa : z + z = a + a := by
    rcases hs2 with ha | hb
    · exact ha
    · rcases ht2 with ha | he
      · exact (hab (ha.symm.trans hb)).elim
      · exact (hbe (hb.symm.trans he)).elim
  constructor
  · rcases hzS with hz | hz | hz
    · exact hz
    · exact (hab (hzaa.symm.trans
        (congrArg (fun w : G => w + w) hz))).elim
    · exact (hab (hzaa.symm.trans
        ((congrArg (fun w : G => w + w) hz).trans
          (pair_sum_translate b b d hd)))).elim
  · rcases hzT with hz | hz | hz
    · exact hz
    · exact (hae (hzaa.symm.trans
        ((congrArg (fun w : G => w + w) hz).trans
          (pair_sum_translate e e u hu)))).elim
    · exact (hae (hzaa.symm.trans
        (((congrArg (fun w : G => w + w) hz).trans
          (pair_sum_translate (e + d) (e + d) u hu)).trans
          (pair_sum_translate e e d hd)))).elim

/-- The normalized exceptional pair shares exactly its singleton when the
additional 2-torsion shift is zero; otherwise its supports are disjoint.
The intersection statement itself does not require d ≠ 0. -/
theorem p2m_local_exceptionalPartner_normalized_inter
    (a b d u : G) (hd : d + d = 0) (hab : a + a ≠ b + b)
    (hu : u + u = 0)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
      ((b - a) + (b - a)) + (b - a) = d) :
    ({a, b, b + d} : Finset G) ∩
        translateSupport ({a, b + b - a, (b + b - a) + d} : Finset G) u =
      if u = 0 then {a} else ∅ := by
  by_cases hu0 : u = 0
  · rw [if_pos hu0]
    ext z
    constructor
    · intro hz
      obtain ⟨hzS, hzT⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_singleton.mpr
        (deltaExceptional_common_mem a b d u z hd hab hu h3 hzS hzT).1
    · intro hz
      have hza : z = a := Finset.mem_singleton.mp hz
      subst z
      apply Finset.mem_inter.mpr
      constructor
      · simp
      · rw [translateSupport_three, hu0]
        simp
  · rw [if_neg hu0]
    ext z
    constructor
    · intro hz
      obtain ⟨hzS, hzT⟩ := Finset.mem_inter.mp hz
      obtain ⟨hza, hzu⟩ :=
        deltaExceptional_common_mem a b d u z hd hab hu h3 hzS hzT
      have hau : a + u = a + 0 := by
        rw [add_zero]
        exact hzu.symm.trans hza
      exact (hu0 (add_left_cancel hau)).elim
    · intro hz
      have hfalse : False := by simpa using hz
      exact hfalse.elim










end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b d u : G),
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
    @Ne.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          a a)
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          b b) →
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
        Or
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
                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHSub.{p2m_u_0} G
                      (@SubNegMonoid.toSub.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                    b a)
                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHSub.{p2m_u_0} G
                      (@SubNegMonoid.toSub.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                    b a))
                (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHSub.{p2m_u_0} G
                    (@SubNegMonoid.toSub.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                  b a))
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
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
                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHSub.{p2m_u_0} G
                      (@SubNegMonoid.toSub.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                    b a)
                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHSub.{p2m_u_0} G
                      (@SubNegMonoid.toSub.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                    b a))
                (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHSub.{p2m_u_0} G
                    (@SubNegMonoid.toSub.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                  b a))
              d) →
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1)
              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) b
                  (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      b d))))
              (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                    (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHSub.{p2m_u_0} G
                        (@SubNegMonoid.toSub.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        b b)
                      a)
                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHSub.{p2m_u_0} G
                            (@SubNegMonoid.toSub.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            b b)
                          a)
                        d))))
                u))
            (@ite.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
              (@Eq.{p2m_u_0 + 1} G u
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
              (inst_1 u
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G) a)
              (@EmptyCollection.emptyCollection.{p2m_u_0} (Finset.{p2m_u_0} G)
                (@Finset.instEmptyCollection.{p2m_u_0} G))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalPartner_normalized_inter

