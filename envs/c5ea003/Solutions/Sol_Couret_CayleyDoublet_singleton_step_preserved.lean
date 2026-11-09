-- Prove2me | solution 1 for Couret.CayleyDoublet.singleton_step_preserved
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:03.861583+00:00
-- url     : https://prove2.me/submissions/f5651909-6035-421a-a9ac-314ff1ec5472

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_isMate
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_unique_of_order_three
import Theorems.Thm_Couret_CayleyDoublet_singletonArc_iff
import Theorems.Thm_Couret_CayleyDoublet_singletonArc_iff_point
import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1

set_option autoImplicit false

/-!
CAYLEY-TWO-COLOUR-FAMILY (14 October 2026).

A directed-graph obstruction derived from *both* intrinsic arc colours.
The universal algebraic theorem is independent of cyclic labels. The
specific ZMod arithmetic is kept in a separate section below. This is an
internal Lean candidate pending a matching-SHA CI compilation.
No academic originality, publication or external review claim.
-/

namespace Couret.CayleyDoublet

section TwoColourObstruction

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Any graph isomorphism preserving the unique intrinsic mate and the
singleton arcs preserves translation by the singleton increment. -/
theorem p2m_local_singleton_step_preserved
    (a b c h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hab : a ≠ b) (habh : a ≠ b + h)
    (hac : a ≠ c) (hach : a ≠ c + h)
    (hthreeT : (a - c) + (a - c) + (a - c) = 0 ∨
      (a - c) + (a - c) + (a - c) = h)
    (f : G ≃ G)
    (hf : ∀ x y, CayleyArc (TripleSupport a b h) x y ↔
      CayleyArc (TripleSupport a c h) (f x) (f y))
    (x : G) :
    f (x + a) = f x + a := by
  have hc0 : a - c ≠ 0 := by
    intro he
    exact hac (sub_eq_zero.mp he)
  have hch : a - c ≠ h := by
    intro he
    apply hach
    calc
      a = (a - c) + c := by abel
      _ = h + c := by rw [he]
      _ = c + h := by abel
  have hmS : ∀ z, IsMate (CayleyArc (TripleSupport a b h)) z (z + h) :=
    fun z => halfTurn_isMate a b h hhalf hne z
  have hmT : ∀ z w, IsMate (CayleyArc (TripleSupport a c h)) z w →
      w = z + h := by
    intro z w hw
    exact (halfTurn_unique_of_order_three a c h hhalf hne
      hc0 hch hthreeT z w).mp hw
  have hs : SingletonArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x (x + a) :=
    (singletonArc_iff_point a b h hhalf hne hab habh x (x + a)).mpr rfl
  have ht := (singletonArc_iff f
    (CayleyArc (TripleSupport a b h)) (CayleyArc (TripleSupport a c h))
    hf (fun z => z + h) (fun z => z + h) hmS hmT x (x + a)).mp hs
  exact (singletonArc_iff_point a c h hhalf hne hac hach
    (f x) (f (x + a))).mp ht




end TwoColourObstruction

end Couret.CayleyDoublet

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b c h : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G a b →
        @Ne.{p2m_u_0 + 1} G a
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              b h) →
          @Ne.{p2m_u_0 + 1} G a c →
            @Ne.{p2m_u_0 + 1} G a
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  c h) →
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
                          a c)
                        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHSub.{p2m_u_0} G
                            (@SubNegMonoid.toSub.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                          a c))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a c))
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
                          a c)
                        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHSub.{p2m_u_0} G
                            (@SubNegMonoid.toSub.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                          a c))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a c))
                    h) →
                ∀ (f : Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G),
                  (∀ (x y : G),
                      Iff
                        (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
                          (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a b h) x y)
                        (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
                          (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a c h)
                          (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1} (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G)
                            G (fun x => G)
                            (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                              (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G G
                              (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_0 + 1} G G))
                            f x)
                          (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1} (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G)
                            G (fun x => G)
                            (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                              (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G G
                              (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_0 + 1} G G))
                            f y))) →
                    ∀ (x : G),
                      @Eq.{p2m_u_0 + 1} G
                        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1} (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G
                          (fun x => G)
                          (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                            (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G G
                            (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_0 + 1} G G))
                          f
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            x a))
                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHAdd.{p2m_u_0} G
                            (@AddCommMagma.toAdd.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                          (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1} (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G)
                            G (fun x => G)
                            (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                              (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G G
                              (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_0 + 1} G G))
                            f x)
                          a) := @_root_.Couret.CayleyDoublet.p2m_local_singleton_step_preserved

